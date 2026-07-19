/-
# Dregg2.Crypto.Deriv.SymbolicEmptinessUnbounded — INGREDIENT (c) of the unbounded-emptiness rung:
the PIGEONHOLE EXCISION, and the composition that makes the emptiness decision `n`-FREE.

`SymbolicEmptiness.lean` decides `∃ w, |w| ≤ n ∧ derives w R = true` (sound AND complete,
`nonemptyWithin_iff_bounded`) and names the unbounded decision `∃ w, derives w R = true` as OPEN,
needing three ingredients. (b) landed in `StepBridge.lean` (`satStep_reachable_finite`: the
sat-filtered reachable set is FINITE up to `≅`). This module lands (c) and composes.

## The excision argument

An accepting run of length `> N` visits `> N + 1` prefix states `derList (v.take k) R`. If only `N`
`≅`-classes are available, two prefixes `i < j` land in the SAME class:
`derList (v.take i) R ≅ derList (v.take j) R`. The segment between them is then DEAD WEIGHT — delete
it. `v.take i ++ v.drop j` is strictly shorter and still accepting, because

  * `derList` factors through concatenation (`derList_append`), so both words end by reading the
    common suffix `v.drop j` off their respective `i`/`j` states;
  * `≅` is preserved by reading a word (`PredRE.sim_derList`, iterating the der-congruence), so the
    two runs land in `≅`-related states;
  * `≅` preserves nullability (`PredRE.sim_null`), so the verdict is UNCHANGED.

Iterating (strong induction on length) drives any accepting word down to length `≤ N`.

## ⚠ WHAT THIS DOES **NOT** NEED — the decidable `≅` is NOT load-bearing here

`SymbolicEmptiness.lean`'s header lists a DECIDABLE `≅` as ingredient (a), and this lane was scoped to
assume it. Assuming it turned out to be UNNECESSARY, and the file says so rather than carrying a
hypothesis it does not use: `≅` appears in the pigeonhole ONLY inside PROOFS (choosing a class
representative, transporting nullability), never inside anything that must RUN. The decision that
runs is `nonemptyWithin`, which was already computable at every fixed depth; what was missing was
only a PROOF that one fixed depth suffices.

So `predRENonemptyDecidable` below carries NO `DecidableRel Sim` hypothesis and no `≅`-decision
argument. A decidable `≅` would buy a *smaller/adaptive* bound (a fixpoint detected at runtime rather
than the a-priori `⊕(pieces R)` count), i.e. PERFORMANCE — not decidability. Ingredient (a) is
demoted from blocker to optimization, and that is stated here so a later lane does not "close" a hole
that is not open.

## Resolution — read this before quoting the result

* The decision is `n`-FREE and genuinely COMPUTABLE: the bound `emptinessBound R = |⊕(pieces R)|` is
  a plain `def` over the computable `pieces`/`toSumSubsets`, NOT a `Classical.choose` of the
  finiteness existential. (`pumpDown` is stated on an ARBITRARY `≅`-bounding list so it also
  consumes `satStep_reachable_finite`'s existential shape directly; `reachableWithin_subset_pieces`
  is the concrete instantiation, re-derived from the same banked lemmas that theorem is built from.)
* It is scoped to `IsDeployed R` — inherited from `nonemptyWithin_iff_bounded`, whose completeness
  half is the leaf-factoring onto the two deployed minterm witnesses. Nothing here widens that.
* `emptinessBound` is ASTRONOMICAL: `toSumSubsets` is a power-set construction, so the bound is
  exponential in `|pieces R|`, and `reachableWithin n` is itself exponential in `n`. This is a
  TERMINATION argument, not a practical algorithm — running `nonemptyWithin (emptinessBound R) R` is
  infeasible for any nontrivial `R`. The `#guard`s below therefore exercise the DECISION at concrete
  depths and the bound's computability SEPARATELY, and do not pretend the composite runs. Making it
  run is exactly what ingredient (a) (adaptive fixpoint) would buy.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.StepBridge
import Mathlib.Data.Fintype.Pigeonhole

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Crypto.Deriv.Combinatorics
open PredRE (Sim der null derives derList pieces steps sim_der sim_derList sim_null
  derives_eq_null_derList)

/-! ## §1 The excision — deleting a `≅`-loop from a run preserves the verdict. -/

/-- **`derList_excise`** — THE excision step. If the prefix states at `i` and `j` are similar, then
cutting the segment `[i, j)` out of `v` lands in a `≅`-related state. Both sides read the SAME
suffix `v.drop j`, from `≅`-related starting states, and `sim_derList` transports similarity across
that read. Purely syntactic: no `Matches`, no `correctness`. -/
theorem derList_excise {R : PredRE} {v : List Value} {i j : Nat}
    (hsim : derList (v.take i) R ≅ derList (v.take j) R) :
    derList (v.take i ++ v.drop j) R ≅ derList v R := by
  have h1 : derList (v.take i ++ v.drop j) R = derList (v.drop j) (derList (v.take i) R) :=
    derList_append _ _ _
  have h2 : derList v R = derList (v.drop j) (derList (v.take j) R) := by
    conv_lhs => rw [← List.take_append_drop j v]
    rw [derList_append]
  rw [h1, h2]
  exact sim_derList hsim (v.drop j)

/-- The excised word is STRICTLY shorter — the progress measure of the pumping induction. -/
theorem excise_length {v : List Value} {i j : Nat} (hij : i < j) (hj : j ≤ v.length) :
    (v.take i ++ v.drop j).length < v.length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

/-- The excised word draws its frames from `v` — so "all frames are candidates" survives excision,
which the pumping induction needs to re-apply the pigeonhole. -/
theorem excise_mem {v : List Value} {i j : Nat} {x : Value}
    (h : x ∈ v.take i ++ v.drop j) : x ∈ v := by
  rcases List.mem_append.mp h with h | h
  · exact List.take_subset _ _ h
  · exact List.drop_subset _ _ h

/-! ## §2 The PIGEONHOLE — a long enough run repeats a `≅`-class.

The counting happens over `Fin`: the `|v| + 1` prefix positions are classified by an index into the
finite `≅`-bounding list `xs`, and `Fintype.exists_ne_map_eq_of_card_lt` supplies the collision.
Note the classifier is chosen with `Classical.choose` — it need not be computable, because it is
consumed only by the PROOF of the bound, never by the decision procedure. -/

/-- **`exists_sim_prefix_pair`** — the pigeonhole proper: if a candidate word `v` is longer than the
`≅`-class budget `xs`, two DISTINCT prefixes of `v` drive `R` into `≅`-related states.

Each prefix state is `≅`-bounded by `xs` because it is genuinely sat-reachable: `v.take k` is a
candidate word of length `≤ k`, so `reachableWithin_complete` puts `derList (v.take k) R` in
`reachableWithin k R`, which `hxs` bounds — UNIFORMLY in `k`, which is exactly the strength
`satStep_reachable_finite` was stated with. -/
theorem exists_sim_prefix_pair {R : PredRE} {xs : List PredRE}
    (hxs : ∀ {n : Nat}, reachableWithin n R ⊆[ (· ≅ ·) ] xs)
    {v : List Value} (hv : ∀ x ∈ v, x ∈ candidates) (hlen : xs.length < v.length + 1) :
    ∃ i j, i < j ∧ j ≤ v.length ∧ derList (v.take i) R ≅ derList (v.take j) R := by
  -- Every prefix state is `≅` to a member of `xs`, named by its INDEX.
  have key : ∀ k : Fin (v.length + 1), ∃ idx : Fin xs.length,
      derList (v.take k.val) R ≅ xs.get idx := by
    intro k
    have hcand : ∀ x ∈ v.take k.val, x ∈ candidates :=
      fun x hx => hv x (List.take_subset _ _ hx)
    have hklen : (v.take k.val).length ≤ k.val := by
      simp only [List.length_take]; omega
    obtain ⟨y, hsim, hy⟩ := hxs _ (reachableWithin_complete (R := R) (n := k.val) hcand hklen)
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hy
    exact ⟨idx, by rw [hidx]; exact hsim⟩
  -- Classify each of the `|v| + 1` prefixes by that index; two must collide.
  let f : Fin (v.length + 1) → Fin xs.length := fun k => (key k).choose
  have hf : ∀ k, derList (v.take k.val) R ≅ xs.get (f k) := fun k => (key k).choose_spec
  -- From a collision at `p < q`, similarity of the two prefix states follows by `sym`/`trans`.
  have mk : ∀ p q : Fin (v.length + 1), p.val < q.val → f p = f q →
      ∃ i j, i < j ∧ j ≤ v.length ∧ derList (v.take i) R ≅ derList (v.take j) R := by
    intro p q hpq hfpq
    refine ⟨p.val, q.val, hpq, Nat.lt_succ_iff.mp q.isLt, ?_⟩
    have hq : derList (v.take q.val) R ≅ xs.get (f p) := by rw [hfpq]; exact hf q
    exact Sim.trans (hf p) (Sim.sym hq)
  have hcard : Fintype.card (Fin xs.length) < Fintype.card (Fin (v.length + 1)) := by
    simpa using hlen
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hab' : a.val ≠ b.val := fun h => hab (Fin.val_inj.mp h)
  rcases Nat.lt_or_gt_of_ne hab' with h | h
  · exact mk a b h hfab
  · exact mk b a h hfab.symm

/-! ## §3 The PUMPING LEMMA — every accepting candidate word collapses under the class budget. -/

/-- **`pumpDown`** — INGREDIENT (c), LANDED: given ANY finite list `xs` that `≅`-bounds sat-filtered
reachability from `R` (exactly `satStep_reachable_finite`'s conclusion), every accepting CANDIDATE
word yields an accepting one of length `≤ |xs|`.

Strong induction on the length (run as an induction on a decreasing fuel `n ≥ |v|`): either `v`
already fits the budget, or the pigeonhole finds a repeated `≅`-class, `derList_excise` deletes the
loop, `sim_null` certifies the shorter word still accepts, and `excise_mem` keeps it a candidate
word so the argument re-applies. -/
theorem pumpDown {R : PredRE} {xs : List PredRE}
    (hxs : ∀ {n : Nat}, reachableWithin n R ⊆[ (· ≅ ·) ] xs) :
    ∀ (v : List Value), (∀ x ∈ v, x ∈ candidates) → derives v R = true →
      ∃ u, u.length ≤ xs.length ∧ derives u R = true := by
  have main : ∀ (n : Nat) (v : List Value), v.length ≤ n → (∀ x ∈ v, x ∈ candidates) →
      derives v R = true → ∃ u, u.length ≤ xs.length ∧ derives u R = true := by
    intro n
    induction n with
    | zero => intro v hlen _ hd; exact ⟨v, by omega, hd⟩
    | succ n ih =>
      intro v hlen hv hd
      by_cases hb : v.length ≤ xs.length
      · exact ⟨v, hb, hd⟩
      · obtain ⟨i, j, hij, hjv, hsim⟩ := exists_sim_prefix_pair hxs hv (by omega)
        have hulen : (v.take i ++ v.drop j).length < v.length := excise_length hij hjv
        have hud : derives (v.take i ++ v.drop j) R = true := by
          rw [derives_eq_null_derList] at hd ⊢
          rw [sim_null (derList_excise hsim)]; exact hd
        exact ih _ (by omega) (fun x hx => hv x (excise_mem hx)) hud
  intro v hv hd
  exact main v.length v (Nat.le_refl _) hv hd

/-! ## §4 The COMPUTABLE bound, and the `n`-FREE decision.

`satStep_reachable_finite` hides its witness behind `∃`, so extracting a NUMBER from it needs
`Classical.choose` and the resulting bound would not run. Its witness is however literally
`⊕(pieces R)`, which is computable — so the containment is re-derived here in WITNESSED form from
the same two banked lemmas (`reachableWithin_mem_steps` + `steps_to_toSumSubsets`) that theorem is
assembled from. That is what keeps `emptinessBound` a plain `def`. -/

/-- The containment of `satStep_reachable_finite`, with the witness EXPOSED rather than existentially
quantified: sat-filtered reachability from `R`, at every depth, sits inside the computable
`⊕(pieces R)` up to `≅`. -/
theorem reachableWithin_subset_pieces {R : PredRE} {n : Nat} :
    reachableWithin n R ⊆[ (· ≅ ·) ] ⊕(pieces R) := fun _ hs =>
  have ⟨_, _, hk⟩ := reachableWithin_mem_steps hs
  PredRE.steps_to_toSumSubsets _ hk

/-- **`emptinessBound R`** — the a-priori word-length budget: the number of `≅`-classes available to
`R`'s derivative state space, over-counted by the size of the finite carrier `⊕(pieces R)`.
COMPUTABLE (`pieces` and `toSumSubsets` are plain `def`s), which is what makes the decision below
run rather than merely exist. ⚠ Exponential in `|pieces R|` — see the header. -/
def emptinessBound (R : PredRE) : Nat := (⊕(pieces R)).length

/-- **`nonempty_iff_nonemptyWithin_bound`** — THE `n`-FREE REDUCTION: for a deployed guard, language
NONEMPTINESS over words of ANY length is EQUIVALENT to the bounded sat-filtered search at the single
fixed depth `emptinessBound R`.

`←` is the bounded soundness (drop the length bound). `→` is the new content: canonicalize the
arbitrary accepting word onto the two deployed minterm witnesses (`derList_factors`), then pump it
down under the class budget (`pumpDown`). This is precisely the statement `SymbolicEmptiness.lean`'s
header records as NOT PROVED. -/
theorem nonempty_iff_nonemptyWithin_bound {R : PredRE} (hR : IsDeployed R) :
    (∃ w, derives w R = true) ↔ nonemptyWithin (emptinessBound R) R = true := by
  rw [nonemptyWithin_iff_bounded hR]
  constructor
  · rintro ⟨w, hw⟩
    have hvc : ∀ x ∈ w.map canonicalWitness, x ∈ candidates := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact canonicalWitness_mem y
    have hvd : derives (w.map canonicalWitness) R = true := by
      rw [derives_eq_null_derList, ← derList_factors w hR, ← derives_eq_null_derList]
      exact hw
    exact pumpDown (fun {n} => reachableWithin_subset_pieces (n := n)) _ hvc hvd
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- **`predRENonemptyDecidable`** — the UNBOUNDED, `n`-FREE emptiness DECISION for a deployed guard:
`Decidable (∃ w, derives w R = true)`, quantifying over words of EVERY length over the infinite
`Value` alphabet.

This is NOT the classically-free `Classical.dec` (which would be vacuous): the instance is built by
`decidable_of_iff` from a COMPUTABLE Boolean — `nonemptyWithin (emptinessBound R) R` — through the
proven reduction. Its content is exactly that reduction. Carries no `DecidableRel Sim` hypothesis;
see the header for why ingredient (a) is an optimization, not a blocker. -/
def predRENonemptyDecidable {R : PredRE} (hR : IsDeployed R) :
    Decidable (∃ w, derives w R = true) :=
  decidable_of_iff _ (nonempty_iff_nonemptyWithin_bound hR).symm

/-- **`nonemptyWithin_bound_complete`** — the contrapositive, which is the whole point: a `false`
verdict at the single depth `emptinessBound R` now proves the language is EMPTY for words of ANY
length. The bounded decision could only ever say "no short word". -/
theorem nonemptyWithin_bound_complete {R : PredRE} (hR : IsDeployed R)
    (h : nonemptyWithin (emptinessBound R) R = false) : ¬ ∃ w, derives w R = true := by
  intro hex
  rw [(nonempty_iff_nonemptyWithin_bound hR).mp hex] at h
  exact Bool.noConfusion h

/-! ## §5 Non-vacuity — the pieces that RUN, run; the pieces that do not, are named.

The composite `nonemptyWithin (emptinessBound R) R` is not evaluable (§header: doubly exponential),
so guarding it would hang rather than bite. What IS guarded is each half on concrete objects: the
bound genuinely computes to a natural number, and the decision genuinely computes at concrete
depths. The theorems above are what joins them. -/

section Guards

open Dregg2.Crypto.HandlebarsGuarded (braceP noDoubleBraceRE)
open PredRE (bot)

/-! ### The bound COMPUTES.

Each of these is a kernel evaluation of `emptinessBound`, i.e. of `|⊕(pieces R)|`. They are the
witness that the bound is a genuine natural number rather than a `Classical.choose` of the
finiteness existential — which is the difference between a decision that RUNS and one that merely
EXISTS (and a merely-existing `Decidable` would be `Classical.dec`, i.e. vacuous). -/

-- `pieces ε = [ε, bot]` (2), and `⊕` is nonempty-subsets-up-to-permutation: 2 + 2 = 4.
#guard emptinessBound PredRE.ε = 4
-- A single leaf has 3 pieces, and `⊕` of a 3-list is 3 + 3·2 + 3! = 15. The power-set blow-up,
-- visible already at the smallest nontrivial machine.
#guard emptinessBound (.sym braceP) = 15
#guard emptinessBound bot = 15

/-! ### END-TO-END: the unbounded decision, kernel-evaluated.

`ε` is the one machine whose budget (4) is small enough that the composite actually runs —
`reachableWithin 4` builds 81 residuals. So on `ε` the FULL `n`-free verdict is discharged by
computation, with no `Classical.choose` anywhere on the path. -/

theorem eps_isDeployed : IsDeployed PredRE.ε := True.intro

#guard nonemptyWithin (emptinessBound PredRE.ε) PredRE.ε = true

/-- THE `n`-FREE DECISION, FIRED: `ε` accepts SOME word of SOME length, concluded from a kernel
evaluation at the single computed depth `emptinessBound ε = 4`. The `rfl` is the decision procedure
running. -/
example : ∃ w, derives w PredRE.ε = true :=
  (nonempty_iff_nonemptyWithin_bound eps_isDeployed).mpr rfl

/-! ### ⚠ The NEGATIVE pole does not RUN — stated precisely, because it is the honest limit.

The smallest EMPTY deployed machine is a single leaf (`bot = sym .ff`), budget 15. `reachableWithin`
grows by a factor of 3 per layer with NO deduplication, so the composite would materialize
`3^15 ≈ 1.4·10^7` residuals — every single one of them literally `bot`. That is out of kernel reach,
so the `false` evaluation is left as a HYPOTHESIS below rather than faked with a `rfl` that would
hang.

This is a PERFORMANCE limit, not a soundness gap: `nonemptyWithin_bound_complete` is proven for
every deployed `R`, and it is exactly what ingredient (a) — a decidable `≅` — buys. With `≅`-dedup
the frontier for `bot` saturates at ONE state and the same verdict falls out at depth 1. Decidability
was never the blocker (see the header); TRACTABILITY is. -/

theorem bot_isDeployed : IsDeployed bot := leafDeployed_ff

/-- The unbounded EMPTINESS verdict, wired end to end with the one un-evaluated step named as a
hypothesis: a `false` at the computed depth proves NO word of ANY length is accepted. -/
example (h : nonemptyWithin (emptinessBound bot) bot = false) : ¬ ∃ w, derives w bot = true :=
  nonemptyWithin_bound_complete bot_isDeployed h

/-! ### The pigeonhole's hypothesis is INHABITED on the real deployed guard. -/

/-- `pumpDown`'s premise holds for the actual templater guard: sat-filtered reachability from
`noDoubleBraceRE` is `≅`-bounded by one fixed computable list, uniformly in the depth. So the
pumping lemma is not quantifying over an empty hypothesis. -/
example : ∀ {n : Nat}, reachableWithin n noDoubleBraceRE ⊆[ (· ≅ ·) ] ⊕(pieces noDoubleBraceRE) :=
  fun {_} => reachableWithin_subset_pieces

/-- ...and the real guard IS deployed, so the `n`-free reduction applies to it — the bound is simply
too large to evaluate. -/
example : IsDeployed noDoubleBraceRE := by
  simp only [noDoubleBraceRE, Dregg2.Crypto.HandlebarsGuarded.BB, PredRE.any, IsDeployed]
  exact ⟨leafDeployed_tt, leafDeployed_braceP, leafDeployed_braceP, leafDeployed_tt⟩

example : (∃ w, derives w noDoubleBraceRE = true) ↔
    nonemptyWithin (emptinessBound noDoubleBraceRE) noDoubleBraceRE = true :=
  nonempty_iff_nonemptyWithin_bound (by
    simp only [noDoubleBraceRE, Dregg2.Crypto.HandlebarsGuarded.BB, PredRE.any, IsDeployed]
    exact ⟨leafDeployed_tt, leafDeployed_braceP, leafDeployed_braceP, leafDeployed_tt⟩)

end Guards

/-! ## Axiom hygiene — the pigeonhole tower is kernel-clean. -/

#assert_all_clean [
  derList_excise, excise_length, excise_mem,
  exists_sim_prefix_pair, pumpDown,
  reachableWithin_subset_pieces,
  nonempty_iff_nonemptyWithin_bound, nonemptyWithin_bound_complete,
  predRENonemptyDecidable
]

end Dregg2.Crypto.Deriv
