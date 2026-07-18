/-
# Dregg2.Crypto.Deriv.StepBridge — INGREDIENT (b) of the unbounded-emptiness rung: the bridge from
CONCRETE `der`-reachability into the SYMBOLIC `step`-finiteness that `Finiteness.der_finite` provides.

## The gap this closes

`SymbolicEmptiness.lean`'s header names three unbanked ingredients for the UNBOUNDED emptiness
decision. Ingredient **(b)** was: `der_finite` bounds `steps` — built on the sat-FREE symbolic
`step r = leaves (𝜕 r)` — whereas tier 2's `satStep r = candidates.map (der · r)` walks CONCRETE
derivatives, and NOTHING related the two. So `der_finite`'s finiteness did not transfer to
`satStep`-reachability, which is exactly what a termination / pigeonhole argument consumes.

## What is proved, at the resolution it actually holds

The containment holds **EXACTLY** — as syntactic list membership, no `≅`-relaxation needed:

  `der_mem_step : ∀ (a : Value) (r : PredRE), der a r ∈ step r`

The `cat`/`star` split with the `firstPred` placeholder was the suspect, and it turns out to be a
NON-obstruction, for a structural reason worth stating: `step` is `leaves (𝜕 r)`, and `leaves`
collects the leaves of BOTH subtrees of every `TTerm.Node`, DISCARDING the branch condition. So the
fact that `firstPred l := .tt` does not faithfully encode the concrete `cat` branch (which tests the
frame-INDEPENDENT `null l`) costs nothing here: whichever way the concrete `der` resolves its
`if null l` test, the corresponding residual is among the leaves, because both branches contribute.
Concretely, `step (cat l r)` contains `productWith alt (map (· ⬝ r) (step l)) (step r)` (covering the
nullable case `alt (cat (der a l) r) (der a r)`) APPENDED to `map (· ⬝ r) (step l)` (covering the
non-nullable case `cat (der a l) r`) — the union of both, so `der` lands in it either way.

This is precisely why the placeholder is harmless for FINITENESS while being fatal for EMPTINESS
(the over-approximation the tier-2 header warns about, and the reason `satStep` exists): the sat-free
`step` is a strict OVER-approximation of the concrete fan-out, and an over-approximation is exactly
what a finiteness bound needs to transfer.

From there:

  * `satStep_subset_step` — `satStep r ⊆ step r` (plain `⊆`; every candidate derivative is a leaf);
  * `reachableWithin_mem_steps` — every sat-reachable residual is in `steps R k` for SOME `k ≤ n`
    (the reflexive `s :: satStep s` growth of `reachableWithin` is why it is a UNION over `k`, not
    `steps R n` on the nose);
  * `satStep_reachable_finite` — **the transfer**: a FIXED finite list bounds `reachableWithin n R`
    up to `≅`, for ALL `n`. Stated in `der_finite`'s exact shape (`∃ xs, ∀ {n}, · ⊆[ (· ≅ ·) ] xs`)
    so the pigeonhole step composes with it directly.

⚠ SCOPE. This is ingredient (b) ALONE. It does NOT decide unbounded emptiness. Ingredients (a) a
DECIDABLE `≅` and (c) the pigeonhole/counting excision remain open exactly as
`SymbolicEmptiness.lean` states them. What (b) buys is that the state space `satStep` walks is now
KNOWN FINITE up to `≅` — the hypothesis a pigeonhole argument needs, previously unavailable.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicEmptiness

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Deriv.Combinatorics
open PredRE (Sim der step steps derivative pieces)

namespace PredRE

/-! ## §1 The core containment — `der a r ∈ step r`, EXACT membership. -/

/-- A `productWith` membership introduction: `op x y` is in the product-with when `x`/`y` are in the
factors. (`productWith op xs ys = map (uncurry op) (xs.product ys)`.) -/
theorem mem_productWith {op : PredRE → PredRE → PredRE} {x y : PredRE} {xs ys : List PredRE}
    (hx : x ∈ xs) (hy : y ∈ ys) : op x y ∈ List.productWith op xs ys := by
  simp only [List.productWith, mem_map, Prod.exists, List.pair_mem_product,
    Function.uncurry_apply_pair]
  exact ⟨x, y, ⟨hx, hy⟩, rfl⟩

/-- **`der_mem_step`** — THE BRIDGE, ingredient (b)'s core: the CONCRETE derivative of `r` w.r.t. ANY
frame `a` is one of the SYMBOLIC step's leaf states. Exact list membership — not merely up to `≅`.

Structural induction on `r`, following `𝜕`'s clauses:
* `ε` — `der a ε = bot` and `step ε = [bot]`;
* `sym φ` — `der` is `ε` or `bot` by the leaf test, and `step (sym φ) = [ε, bot]` lists BOTH (the
  `TTerm.Node φ` branch condition is discarded by `leaves`);
* `alt`/`inter` — the two IHs pair up under `productWith`;
* `neg`/`star` — the IH maps through the unary lift;
* `cat l r` — the interesting one: the concrete `if null l` picks `alt (cat (der a l) r) (der a r)`
  or `cat (der a l) r`, and `step (cat l r)` is the APPEND of a list containing the former and a list
  containing the latter. The `firstPred` placeholder condition is irrelevant because `leaves` takes
  both subtrees. -/
theorem der_mem_step (a : Value) : ∀ (r : PredRE), der a r ∈ step r := by
  intro r
  induction r with
  | ε =>
      simp only [der, step, derivative, leaves]
      exact mem_singleton.mpr rfl
  | sym φ =>
      simp only [der, step, derivative, leaves]
      split <;> simp
  | alt l r ihl ihr =>
      simp only [der, step_alt]
      exact mem_productWith ihl ihr
  | inter l r ihl ihr =>
      simp only [der, step_inter]
      exact mem_productWith ihl ihr
  | cat l r ihl ihr =>
      rw [step_cat, leaves_unary]
      have hcat : PredRE.cat (der a l) r ∈ map (fun x => PredRE.cat x r) (step l) :=
        mem_map.mpr ⟨der a l, ihl, rfl⟩
      simp only [der]
      split
      · -- nullable left: `alt (cat (der a l) r) (der a r)` sits in the `productWith` half.
        exact mem_append.mpr (Or.inl (mem_productWith hcat ihr))
      · -- non-nullable left: `cat (der a l) r` sits in the appended `map` half.
        exact mem_append.mpr (Or.inr hcat)
  | star r ih =>
      simp only [der, step_star]
      exact mem_map.mpr ⟨der a r, ih, rfl⟩
  | neg r ih =>
      simp only [der, step_neg]
      exact mem_map.mpr ⟨der a r, ih, rfl⟩

end PredRE

/-! ## §2 Transfer — `satStep ⊆ step`, and sat-reachability lands in `steps`. -/

/-- **`satStep_subset_step`** — the sat-FILTERED step is contained in the sat-FREE symbolic step.
Immediate from `der_mem_step`: every `satStep` residual is `der a r` for a candidate frame `a`, and
every such concrete derivative is a `step` leaf. (The inclusion is STRICT in general — that is the
whole point of `satStep`: `step` also lists residuals reachable only through UNSAT branches, which is
harmless for finiteness and fatal for emptiness.) -/
theorem satStep_subset_step (r : PredRE) : satStep r ⊆ step r := by
  intro s hs
  simp only [satStep, List.mem_map] at hs
  obtain ⟨a, _, rfl⟩ := hs
  exact PredRE.der_mem_step a r

/-- One symbolic layer: a `step` successor of a state in `steps R k` is in `steps R (k+1)`. -/
theorem mem_steps_succ {R t s : PredRE} {k : Nat} (ht : t ∈ steps R k) (hs : s ∈ step t) :
    s ∈ steps R (k + 1) := by
  simp only [steps, mem_flatten, mem_map, exists_exists_and_eq_and]
  exact ⟨t, ht, hs⟩

/-- **`reachableWithin_mem_steps`** — every residual the CONCRETE sat-filtered search reaches within
`n` steps is a SYMBOLIC state: it lies in `steps R k` for some `k ≤ n`.

It is a union over `k`, not `steps R n` on the nose, because `reachableWithin` grows REFLEXIVELY
(`s :: satStep s`) — it accumulates every intermediate depth rather than the exact frontier. That is
fine for the transfer: `der_finite` bounds `steps R k` UNIFORMLY in `k`. -/
theorem reachableWithin_mem_steps :
    ∀ {n : Nat} {R s : PredRE}, s ∈ reachableWithin n R → ∃ k, k ≤ n ∧ s ∈ steps R k := by
  intro n
  induction n with
  | zero =>
      intro R s h
      rw [reachableWithin, List.mem_singleton] at h
      subst h
      exact ⟨0, Nat.le_refl 0, by simp only [steps, mem_cons, not_mem_nil, or_false]⟩
  | succ n ih =>
      intro R s h
      rw [reachableWithin, List.mem_flatMap] at h
      obtain ⟨t, ht, hs⟩ := h
      obtain ⟨k, hkn, hk⟩ := ih ht
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨k, Nat.le_succ_of_le hkn, hk⟩
      · exact ⟨k + 1, Nat.succ_le_succ hkn, mem_steps_succ hk (satStep_subset_step t hs)⟩

/-! ## §3 The capstone — sat-filtered reachability is FINITE up to `≅`. -/

/-- **`satStep_reachable_finite`** — INGREDIENT (b), LANDED: there is a FIXED finite list of regexes
containing, UP TO SIMILARITY `≅`, every residual reachable from `R` by ANY number of sat-filtered
concrete-derivative steps.

Stated in `der_finite`'s exact shape (`∃ xs, ∀ {n}, · ⊆[ (· ≅ ·) ] xs`) so the pigeonhole step
consumes the two uniformly. The witness list is the same `⊕(pieces R)` — the concrete search cannot
escape the symbolic over-approximation's bound.

⚠ This gives FINITENESS of the state space, NOT a decision: pigeonholing it into "an accepting word
implies a short one" additionally needs a DECIDABLE `≅` (ingredient (a)) and the counting argument
(ingredient (c)), both still open. -/
theorem satStep_reachable_finite {R : PredRE} :
    ∃ xs : List PredRE, ∀ {n : Nat}, reachableWithin n R ⊆[ (· ≅ ·) ] xs :=
  ⟨⊕(pieces R), fun _ hs =>
    have ⟨_, _, hk⟩ := reachableWithin_mem_steps hs
    PredRE.steps_to_toSumSubsets _ hk⟩

/-! ## §4 Non-vacuity — the containment is exhibited on concrete objects.

Kernel-checked witnesses that `der a r` genuinely appears among `step r`'s leaves (and that the
bridge's consumers are inhabited), rather than the statement holding vacuously. -/

section Guards

open Dregg2.Crypto.HandlebarsGuarded (braceP braceVal dataVal)
open PredRE (bot)

/-! ### Kernel-COMPUTED witnesses.

`PredRE` has no computable `DecidableEq` (`Monotone.lean:31` supplies only a *noncomputable*
classical one), so membership cannot be `decide`d directly. These `#guard`s instead compute both
sides and compare their `Repr` renderings — a genuine evaluation exhibiting the concrete derivative
literally among the symbolic leaves, INDEPENDENT of `der_mem_step`'s proof term (so they would still
bite if the theorem were vacuous or misstated). -/

-- `der braceVal (sym braceP)` is computed and found among `step (sym braceP)`'s leaves.
#guard ((step (.sym braceP)).map reprStr).contains (reprStr (der braceVal (.sym braceP)))

-- The `cat` case with a NULLABLE left factor — the `firstPred`-placeholder suspect, computed.
#guard ((step (.cat (.star (.sym braceP)) (.sym braceP))).map reprStr).contains
  (reprStr (der braceVal (.cat (.star (.sym braceP)) (.sym braceP))))

-- The `cat` case with a NON-nullable left factor (the other concrete branch).
#guard ((step (.cat (.sym braceP) (.sym braceP))).map reprStr).contains
  (reprStr (der braceVal (.cat (.sym braceP) (.sym braceP))))

-- The `star` case.
#guard ((step (.star (.sym braceP))).map reprStr).contains
  (reprStr (der braceVal (.star (.sym braceP))))

-- The inclusion `satStep ⊆ step` computes on `bot`...
#guard ((satStep bot).map reprStr).all (fun s => ((step bot).map reprStr).contains s)
-- ...and is STRICT: `step bot = [ε, bot]` lists the nullable `ε`, reachable only through the UNSAT
-- `.ff` branch, which `satStep bot = [bot, bot]` correctly omits. So the bridge really is a
-- containment in a proper OVER-approximation — not a disguised equality.
#guard !(((step bot).map reprStr).all (fun s => ((satStep bot).map reprStr).contains s))

/-- The deployed guard leaf `sym braceP`, derived under the real brace witness, IS a symbolic leaf.
`der braceVal (sym braceP) = ε` (the leaf fires) and `step (sym braceP) = [ε, bot]`. -/
example : der braceVal (.sym braceP) ∈ step (.sym braceP) := PredRE.der_mem_step braceVal _

/-- ...and under the NON-brace witness, where the concrete derivative is the OTHER leaf (`bot`).
Both polarities of the leaf test land — the `sym` case is not one-sided. -/
example : der dataVal (.sym braceP) ∈ step (.sym braceP) := PredRE.der_mem_step dataVal _

/-- The `star` case on a real deployed guard: `der a (star (sym braceP)) = cat (der a _) (star _)`,
which is in `map (· ⬝ star _) (step _)`. -/
example : der braceVal (.star (.sym braceP)) ∈ step (.star (.sym braceP)) :=
  PredRE.der_mem_step braceVal _

/-- The `cat` case — THE suspect constructor (the `firstPred` placeholder split) — exhibited on a
NULLABLE left factor, where the concrete derivative takes the `alt` branch that the placeholder
condition does not encode. It lands anyway, because `leaves` takes both subtrees. -/
example : der braceVal (.cat (.star (.sym braceP)) (.sym braceP))
    ∈ step (.cat (.star (.sym braceP)) (.sym braceP)) := PredRE.der_mem_step braceVal _

/-- ...and on a NON-nullable left factor, where the concrete derivative takes the other branch. -/
example : der braceVal (.cat (.sym braceP) (.sym braceP))
    ∈ step (.cat (.sym braceP) (.sym braceP)) := PredRE.der_mem_step braceVal _

/-- The transfer is inhabited on the real deployed guard: sat-filtered reachability from
`noDoubleBraceRE` is bounded, at every depth, by one fixed finite list up to `≅`. -/
example : ∃ xs : List PredRE,
    ∀ {n : Nat}, reachableWithin n Dregg2.Crypto.HandlebarsGuarded.noDoubleBraceRE
      ⊆[ (· ≅ ·) ] xs := satStep_reachable_finite

end Guards

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene — the bridge is kernel-clean. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.mem_productWith,
  Dregg2.Crypto.Deriv.PredRE.der_mem_step,
  Dregg2.Crypto.Deriv.satStep_subset_step,
  Dregg2.Crypto.Deriv.mem_steps_succ,
  Dregg2.Crypto.Deriv.reachableWithin_mem_steps,
  Dregg2.Crypto.Deriv.satStep_reachable_finite
]
