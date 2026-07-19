/-
# Dregg2.Crypto.Deriv.SymbolicDecision — THE ASSEMBLY: the end-to-end symbolic emptiness decision,
# `Decidable (∃ w, derives w R = true)`, as ONE fragment-typed instance.

`SymbolicEmptiness.lean` decides the BOUNDED problem `∃ w, |w| ≤ n ∧ derives w R = true`
(`nonemptyWithin_iff_bounded`, sound AND complete). `StepBridge.lean` transfers `der_finite`'s
finiteness onto the concrete sat-filtered search (`satStep_reachable_finite`: the reachable state
space is FINITE up to `≅`, for ALL depths, bounded by the computable `⊕(pieces R)`).
`SymbolicEmptinessUnbounded.lean` composes them into the `n`-FREE decision
(`predRENonemptyDecidable`): pigeonhole gives the length bound `emptinessBound R = |⊕(pieces R)|`,
and the bounded decision at that single depth settles words of EVERY length.

This module is the CAPSTONE: it names the PRECISE fragment the decision lives on — the deployed-guard
fragment `IsDeployed` — as a TYPE (`DeployedRE = {R : PredRE // IsDeployed R}`), and packages the
composition as a single `Decidable` INSTANCE on that type. That makes the decision usable by `decide`
and typeclass resolution, and lets a `#guard` fire the WHOLE assembled stack (instance resolution +
kernel reduction) end to end.

## The fragment — stated precisely, and it is the COMMON one (no mismatch)

Both composed halves live on the SAME fragment, `IsDeployed R`:
  * `nonemptyWithin_iff_bounded` needs `IsDeployed R` — its completeness half is the leaf-factoring of
    an arbitrary accepting `Value` word onto the two deployed minterm witnesses `[braceVal, dataVal]`
    (`derList_factors`), which holds exactly when every `sym` leaf reads a frame only through
    `leaf braceP` (`LeafDeployed`).
  * the pigeonhole (`pumpDown`/`nonempty_iff_nonemptyWithin_bound`) ALSO needs `IsDeployed R`, and for
    the SAME reason — it canonicalizes the accepting word onto candidates before pumping.
  * `satStep_reachable_finite` needs NOTHING (holds for all `R`); it is the ambient finiteness the
    pigeonhole consumes, so it does not narrow the fragment.
So the common — and only — fragment is `IsDeployed`. There is no fragment mismatch between the bounded
decision and the pigeonhole to reconcile: they were carved for the same guard algebra. `DeployedRE`
bundles exactly that predicate and nothing wider.

## What RUNS, and the honest tractability pole (unchanged from the pieces)

The assembled decision is genuinely COMPUTABLE — built by `decidable_of_iff` from the Boolean
`nonemptyWithin (emptinessBound R) R`, NOT `Classical.dec` (which would be vacuous). But
`emptinessBound` is astronomical (`⊕` is a power-set; `reachableWithin` grows ×3 per layer with NO
dedup), so the composite only kernel-evaluates when the bound is tiny.

  * POSITIVE pole RUNS: `ε` has bound `4`, so the assembled `n`-free instance DECIDES `ε` nonempty by
    kernel evaluation through `decide` — the whole stack, fired (`decision_fires_eps`).
  * NEGATIVE pole is INTRACTABLE at the `n`-free depth: the smallest empty deployed machine is a
    single leaf (`bot`/`contradictionRE`), whose bound is `≥ 15`, i.e. `3^15 ≈ 1.4·10⁷` residuals —
    out of kernel reach. So `false` at the `n`-free depth is a proven SOUND verdict left as a
    hypothesis (`contradiction_empty_of_bound_false`), NOT a `rfl` that would hang. What DOES run on
    the empty machine is the sound+COMPLETE BOUNDED decision at a small depth
    (`contradiction_no_short_word`): a complete `false` for words of length `≤ 3`.

This is a PERFORMANCE limit, not a soundness gap (`nonemptyWithin_bound_complete` is proven for every
deployed `R`), and it is exactly what ingredient (a) — a decidable `≅` giving frontier DEDUP, already
banked as `AciComplete.simDecide` on `RigidFull` — would buy. Wiring that dedup into `reachableWithin`
(and re-proving the pigeonhole against the dedup'd frontier) is a separate lane; nothing here fakes it.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicEmptinessUnbounded

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open PredRE (derives)

/-! ## §1 The fragment as a TYPE. -/

/-- **`DeployedRE`** — the deployed-guard fragment, bundled: a `PredRE` together with a proof that it
is a guard the deployed templater fragment can write (`IsDeployed`, i.e. every `sym` leaf reads a
frame only through `leaf braceP`). This is the PRECISE — and common — fragment on which the symbolic
emptiness decision is both sound and complete. -/
abbrev DeployedRE : Type := {R : PredRE // IsDeployed R}

/-! ## §2 The end-to-end decision, as ONE instance. -/

/-- **`predRE_emptiness_decidable`** — THE ASSEMBLY: the `n`-FREE symbolic emptiness decision for a
deployed guard, `Decidable (∃ w, derives w R = true)`, quantifying over words of EVERY length over the
infinite `Value` alphabet. It is the single composition of the three banked pieces
(`satStep_reachable_finite` ⟹ pigeonhole `pumpDown` ⟹ `nonemptyWithin_iff_bounded` at the computable
depth `emptinessBound R`), delivered by `predRENonemptyDecidable`, now carrying its fragment as the
type `DeployedRE` rather than a loose hypothesis. NOT `Classical.dec`: `decide` runs it (see §3). -/
def predRE_emptiness_decidable (R : DeployedRE) :
    Decidable (∃ w, derives w R.val = true) :=
  predRENonemptyDecidable R.property

/-- Registered as an INSTANCE on the fragment type, so `decide`/typeclass resolution find the decision
for any bundled deployed guard. -/
instance instDecidableNonemptyDeployed (R : DeployedRE) :
    Decidable (∃ w, derives w R.val = true) :=
  predRE_emptiness_decidable R

/-! ## §3 The decision FIRES — the positive pole runs through the assembled instance. -/

/-- `ε` bundled into the fragment (accepts every leaf vacuously — no `sym` nodes). -/
def epsDeployed : DeployedRE := ⟨PredRE.ε, eps_isDeployed⟩

/-- **`decision_fires_eps`** — the WHOLE assembled stack, fired: the `n`-free instance decides `ε`
nonempty (`emptinessBound ε = 4`, so `reachableWithin 4` materialises and `.any null` bites) — instance
resolution + `decidable_of_iff` reduction + kernel evaluation, all through `decide`. The `rfl` is the
composed decision procedure running. -/
theorem decision_fires_eps :
    (@decide _ (predRE_emptiness_decidable epsDeployed)) = true := by rfl

/-- The proposition itself, concluded FROM the running instance: `ε` accepts some word of some length,
by kernel evaluation of the assembled `n`-free decision (instance passed explicitly, since the
proposition is stated on the bare `PredRE.ε` rather than a bundled `.val`). -/
example : ∃ w, derives w PredRE.ε = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable epsDeployed) decision_fires_eps

/-! ## §4 The negative pole — the empty machine, at both resolutions.

`contradictionRE = (sym braceP) ⋒ (sym ¬braceP)` — one frame constrained to be a brace AND not a
brace; genuinely empty. It IS deployed (its leaves are `braceP` and `¬braceP`). -/

/-- `contradictionRE` is in the fragment (both leaves are `LeafDeployed`). -/
theorem contradiction_isDeployed : IsDeployed contradictionRE := by
  simp only [contradictionRE, IsDeployed]
  exact ⟨leafDeployed_braceP, leafDeployed_not_braceP⟩

/-- `contradictionRE` bundled. -/
def contradictionDeployed : DeployedRE := ⟨contradictionRE, contradiction_isDeployed⟩

/-- **`contradiction_no_short_word`** — the sound+COMPLETE BOUNDED decision, RUN on the empty machine:
`nonemptyWithin 3 contradictionRE` kernel-evaluates `false`, and `nonemptyWithin_iff_bounded` makes
that a COMPLETE verdict — NO accepting word of length `≤ 3` exists (not merely "the search found
none"). This is the `false` pole the assembled decision delivers at a tractable depth. -/
theorem contradiction_no_short_word :
    ¬ ∃ w, w.length ≤ 3 ∧ derives w contradictionRE = true := by
  rw [← nonemptyWithin_iff_bounded (n := 3) contradiction_isDeployed]
  decide

/-- **`contradiction_empty_of_bound_false`** — the `n`-FREE `false` verdict, wired end to end with the
one intractable kernel step named as a hypothesis: a `false` at the computed depth
`emptinessBound contradictionRE` proves NO word of ANY length is accepted. `nonemptyWithin_bound_complete`
is PROVEN for every deployed guard; only the kernel evaluation of `nonemptyWithin (emptinessBound …)`
is out of reach (`3^15+` residuals, every one `bot`-like) — a performance limit, not a soundness gap,
exactly what frontier `≅`-dedup would close. -/
theorem contradiction_empty_of_bound_false
    (h : nonemptyWithin (emptinessBound contradictionRE) contradictionRE = false) :
    ¬ ∃ w, derives w contradictionRE = true :=
  nonemptyWithin_bound_complete contradiction_isDeployed h

/-! ## §5 Non-vacuity `#guard`s — the assembled decision, kernel-evaluated at both poles. -/

section Guards

-- POSITIVE pole: the assembled `n`-free instance DECIDES a satisfiable deployed guard `true`,
-- through `decide` (instance resolution + composed reduction), on the one machine whose bound (4) is
-- small enough to run.
#guard @decide _ (predRE_emptiness_decidable epsDeployed)

-- NEGATIVE pole (tractable resolution): the sound+complete BOUNDED decision kernel-evaluates FALSE on
-- the empty `contradictionRE` at depth 3 — a COMPLETE verdict for words of length ≤ 3. The `n`-free
-- FALSE at depth `emptinessBound` is the same verdict, intractable to evaluate (see
-- `contradiction_empty_of_bound_false`).
#guard nonemptyWithin 3 contradictionRE = false

-- ...and the SAT/UNSAT split is genuine: the same `contradictionRE` is empty while `sym braceP`
-- (a real brace guard) is nonempty at bound 1 — the sat-filter is load-bearing, not a constant.
#guard nonemptyWithin 1 (.sym Dregg2.Crypto.HandlebarsGuarded.braceP) = true

end Guards

/-! ## Axiom hygiene — the assembly is kernel-clean. -/

#assert_all_clean [
  predRE_emptiness_decidable,
  decision_fires_eps,
  contradiction_isDeployed,
  contradiction_no_short_word,
  contradiction_empty_of_bound_false
]

end Dregg2.Crypto.Deriv
