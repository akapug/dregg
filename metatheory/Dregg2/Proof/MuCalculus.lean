/-
# Dregg2.Proof.MuCalculus — a shallow positive modal-μ calculus over the dregg2 transition system,
with the CTL operators of `Proof/CTL.lean` recovered as named μ/ν-formulae.

`Proof/CTL.lean` gave the eight CTL modalities directly as `OrderHom.lfp`/`gfp` of hand-written
fixpoint BODIES (`euBody`, `egBody`, `agBody`, …) over the complete lattice `Set System.Config`. That
is the *semantic* presentation: each operator is already a fixpoint, but the recursion is baked into
its definition. The modal **μ-calculus** is the *syntactic* presentation — a tiny language of formulae
with explicit `μ`/`ν` binders, interpreted (`denote`) into `Set System.Config`, in which EVERY CTL
operator is a derived abbreviation: `EF P = μx. P ∨ ◇x`, `AG P = νx. P ∧ □x`, and so on. This module
builds that language and PROVES the encoding: each CTL operator from `Proof/CTL.lean` is literally the
denotation of its standard μ-formula (`encode_EX`, `encode_EF`, `encode_AG`, …).

## The shallow, positive embedding (the model decision)

We keep the embedding **shallow** (interpretation directly into `Set Config`, relative to an
environment `ρ : Var → Set Config` for the recursion variables) and **positive by construction**: the
`Formula` inductive has NO negation constructor, so every constructor is monotone in every subformula,
and `bodyHom` (the body of a `μ`/`ν` as a function of the bound variable's slot) is ALWAYS monotone —
`μ`/`ν` are therefore always well-defined via `OrderHom.lfp`/`gfp`, with no syntactic-positivity side
condition and no well-foundedness obligation that would tempt a `sorry`. Negation of a STATE predicate
is still available — embed the complemented set directly as `.atom Pᶜ` — which is all the CTL De Morgan
duals (`EX_AX_dual`, `EF_EG_dual` in `CTL.lean`) ever need; recursion variables never appear negated,
which is exactly the positivity the literature requires for `μ`/`ν` to exist.

ALTERNATIVE (not taken): a fully syntactic μ-calculus WITH a `neg` constructor gated by a separate
`Positive`/`even-occurrence` predicate that `μ`/`ν` carry as a proof obligation. That is more faithful
to the textbook syntax but raises the well-definedness of `lfp`/`gfp` to a real obligation (the body is
only monotone *given* positivity). The shallow positive embedding proves the same encoding theorems
with no `sorry`, so we take it; the negation-of-atoms escape hatch loses nothing the metatheory uses.

## What is PROVED

* `denote_mono` — the denotation is monotone in the environment (the backbone making `bodyHom`
  monotone, hence `μ`/`ν` well-defined). Structural induction over `Formula`.
* `mu_unfold` / `nu_unfold` — the fixpoint (unfolding) laws for the binders, from `map_lfp`/`map_gfp`.
* `encode_EX`, `encode_AX`, `encode_EU`, `encode_AU`, `encode_EF`, `encode_AF`, `encode_EG`, `encode_AG`
  — EACH CTL operator equals the denotation of its standard μ/ν-formula. The headline: the syntactic
  μ-calculus is faithful to the semantic CTL of `Proof/CTL.lean`.

## TEETH (non-vacuity — the embedding is faithful, and the μ/ν alternation genuinely matters)

The `encode_*` theorems ARE the primary teeth: they prove the embedding is not decorative (a vacuous
`denote` could never equal the genuine `EF`/`AG`). On top of that we reuse `CTL.branchSys` (the `Fin 3`
branching witness `0 → 1`, `0 → 2`, `1 ↺`, `2 ↺`) to prove a **fixpoint-alternation** separation:
the μ-formula `μx. {1} ∨ ◇x` (= `EF {1}`) CONTAINS the root `0`, while the ν-formula `νx. {1}ᶜ ∧ □x`
(= `AG {1}ᶜ`) does NOT — i.e. swapping `μ`→`ν` and the polarity flips membership of `0`. This is the
De Morgan dual `EF P = (AG Pᶜ)ᶜ` made concrete on the witness, and it is FALSE if either fixpoint
collapsed to the other. Decidable, finite, refutation-proved.

Pure; spec-first; `#assert_axioms` pins every keystone. No `sorry`/`axiom`/`admit`/`native_decide`.
-/
import Dregg2.Proof.CTL
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Function.Basic

namespace Dregg2.Proof.MuCalculus

open Dregg2.Execution Dregg2.Proof.CTL

/-! ## §0 — The syntax: positive modal-μ formulae over a `System`.

Recursion variables are `Nat`-indexed (`Var`); an environment `Env S` assigns each variable a current
denotation. `Formula S` has only monotone constructors (no `neg`), so positivity is by construction. -/

/-- Recursion-variable names (the binders `μ x. …` / `ν x. …`). `Nat`-indexed; finitely used. -/
abbrev Var := Nat

/-- An environment assigning each recursion variable its current denotation (a set of configs). -/
abbrev Env (S : System) := Var → Set S.Config

/-- **Positive modal-μ formulae over `System S`.** No negation constructor — every constructor is
monotone in every subformula slot — so `μ`/`ν` are always well-defined (no positivity side condition).
Negation of a *state predicate* is available via `.atom Pᶜ` (atoms carry no recursion variable). -/
inductive Formula (S : System) where
  | atom : Set S.Config → Formula S            -- a state predicate (an atomic proposition / its ᶜ)
  | var  : Var → Formula S                       -- a recursion variable
  | or_  : Formula S → Formula S → Formula S     -- ∨ (set union)
  | and_ : Formula S → Formula S → Formula S     -- ∧ (set intersection)
  | dia  : Formula S → Formula S                 -- ◇ / EX (existential modal next)
  | box  : Formula S → Formula S                 -- □ / AX (universal modal next)
  | mu   : Var → Formula S → Formula S           -- μ x. body — least fixpoint binding `x`
  | nu   : Var → Formula S → Formula S           -- ν x. body — greatest fixpoint binding `x`

/-! ## §1 — The denotation `denote` and the binder bodies as `OrderHom`.

`denote S φ ρ : Set S.Config` interprets `φ` relative to environment `ρ`. The `μ`/`ν` cases close the
body in the bound variable's slot as an `OrderHom` (via `bodyHom`) and take its `lfp`/`gfp`.

`denote` and `bodyHom` are mutually defined: `bodyHom S a ρ x` packages `fun X => denote S a (ρ[x↦X])`
with its monotonicity proof, which itself needs `denote_mono` — so we define the bare `denoteFun`
first (structural, no monotonicity bundled), prove `denote_mono`, then bundle `bodyHom` and set
`denote := denoteFun`. The bare recursion makes `μ`/`ν` use `lfp`/`gfp` of the explicitly-bundled hom. -/

variable {S : System}

/-- The bare denotation (no `OrderHom` bundling). The `μ`/`ν` cases take the `lfp`/`gfp` of the body
function directly — well-typed because `Set S.Config` is a complete lattice and (once `denote_mono`
holds) the body is monotone; `lfp`/`gfp` of a NON-monotone function is still *defined* (it is just
`sInf {a | f a ≤ a}` / `sSup {a | a ≤ f a}` of the bare `OrderHom.lfp` requires a hom — so here we use
the `sInf`/`sSup` directly to break the dependency, then prove they coincide with the `OrderHom`
versions once monotonicity is available). To keep `μ`/`ν` standing on the proper `OrderHom.lfp`, we
instead define `denote` AFTER `denote_mono`; this bare version exists only to state `denote_mono`. -/
def denoteFun (S : System) : Formula S → Env S → Set S.Config
  | .atom P,  _ => P
  | .var x,   ρ => ρ x
  | .or_ a b, ρ => denoteFun S a ρ ∪ denoteFun S b ρ
  | .and_ a b, ρ => denoteFun S a ρ ∩ denoteFun S b ρ
  | .dia a,   ρ => pre S (denoteFun S a ρ)
  | .box a,   ρ => preAll S (denoteFun S a ρ)
  | .mu x a,  ρ => sInf { Y | denoteFun S a (Function.update ρ x Y) ⊆ Y }
  | .nu x a,  ρ => sSup { Y | Y ⊆ denoteFun S a (Function.update ρ x Y) }

/-- **`denoteFun_mono` (PROVED)** — the denotation is monotone in the environment: if `ρ x ⊆ σ x` for
every variable `x`, then `denoteFun S φ ρ ⊆ denoteFun S φ σ`. Structural induction on `φ`; the `μ`/`ν`
cases use that the body is monotone in `ρ` *uniformly in the bound slot* (the `Function.update` only
overwrites slot `x`, and the bound `Y` is the same on both sides). This is the backbone that makes the
binder bodies monotone, hence `μ`/`ν` well-defined as genuine `lfp`/`gfp`. -/
theorem denoteFun_mono (φ : Formula S) :
    ∀ {ρ σ : Env S}, (∀ x, ρ x ⊆ σ x) → denoteFun S φ ρ ⊆ denoteFun S φ σ := by
  induction φ with
  | atom P => intro ρ σ _; exact le_refl _
  | var x => intro ρ σ h; exact h x
  | or_ a b iha ihb =>
      intro ρ σ h
      exact Set.union_subset_union (iha h) (ihb h)
  | and_ a b iha ihb =>
      intro ρ σ h
      exact Set.inter_subset_inter (iha h) (ihb h)
  | dia a iha =>
      intro ρ σ h
      exact pre_mono S (iha h)
  | box a iha =>
      intro ρ σ h
      exact preAll_mono S (iha h)
  | mu x a iha =>
      intro ρ σ h
      -- `sInf` of the σ-prefixed-points ⊇ each ρ-prefixed point's body, so the ρ-`sInf` is ≤.
      refine sInf_le_sInf ?_
      intro Y hY
      -- `hY : denoteFun a (σ[x↦Y]) ⊆ Y`; show `denoteFun a (ρ[x↦Y]) ⊆ Y` (then `Y` is a ρ-prefixed pt).
      refine subset_trans (iha ?_) hY
      intro z
      rcases eq_or_ne z x with rfl | hz
      · simp [Function.update_self]
      · simp only [Function.update_of_ne hz]; exact h z
  | nu x a iha =>
      intro ρ σ h
      -- dual: each ρ-postfixed point is a σ-postfixed point, so the σ-`sSup` is ≥.
      refine sSup_le_sSup ?_
      intro Y hY
      -- `hY : Y ⊆ denoteFun a (ρ[x↦Y])`; show `Y ⊆ denoteFun a (σ[x↦Y])`.
      refine subset_trans hY (iha ?_)
      intro z
      rcases eq_or_ne z x with rfl | hz
      · simp [Function.update_self]
      · simp only [Function.update_of_ne hz]; exact h z

/-- The denotation, named `denote` (definitionally `denoteFun`). Throughout we use this name; its
`μ`/`ν` cases are `sInf`/`sSup` of the (now-known-monotone, via `denoteFun_mono`) body. -/
abbrev denote (S : System) (φ : Formula S) (ρ : Env S) : Set S.Config := denoteFun S φ ρ

/-- The body of a binder `μ x. a` / `ν x. a` as a bona-fide `OrderHom (Set S.Config) (Set S.Config)`:
`fun X => denote S a (ρ[x↦X])`, monotone by `denoteFun_mono` (only slot `x` varies). This is the hom
whose `lfp`/`gfp` we prove the binder denotation equals — the bridge from the bare `sInf`/`sSup` in
`denoteFun` to the `OrderHom.lfp`/`gfp` calculus (and thus to `CTL.lean`'s `*Body.lfp`/`gfp`). -/
def bodyHom (S : System) (a : Formula S) (ρ : Env S) (x : Var) :
    Set S.Config →o Set S.Config :=
  ⟨fun X => denote S a (Function.update ρ x X), by
    intro X Y hXY
    refine denoteFun_mono a ?_
    intro z
    rcases eq_or_ne z x with rfl | hz
    · simpa [Function.update_self] using hXY
    · simp only [Function.update_of_ne hz]; exact le_refl _⟩

@[simp] theorem bodyHom_apply (a : Formula S) (ρ : Env S) (x : Var) (X : Set S.Config) :
    bodyHom S a ρ x X = denote S a (Function.update ρ x X) := rfl

/-- **`denote_mu` (PROVED)** — the binder `μ` denotation IS the `OrderHom.lfp` of its body. The bare
`sInf` in `denoteFun` coincides with `(bodyHom …).lfp` because `bodyHom`'s underlying function is
exactly `fun X => denote S a (ρ[x↦X])`, so the prefixed-point sets are equal. -/
theorem denote_mu (x : Var) (a : Formula S) (ρ : Env S) :
    denote S (.mu x a) ρ = (bodyHom S a ρ x).lfp := by
  show sInf { Y | denoteFun S a (Function.update ρ x Y) ⊆ Y } = (bodyHom S a ρ x).lfp
  rfl

/-- **`denote_nu` (PROVED)** — dually, the binder `ν` denotation IS the `OrderHom.gfp` of its body. -/
theorem denote_nu (x : Var) (a : Formula S) (ρ : Env S) :
    denote S (.nu x a) ρ = (bodyHom S a ρ x).gfp := by
  show sSup { Y | Y ⊆ denoteFun S a (Function.update ρ x Y) } = (bodyHom S a ρ x).gfp
  rfl

/-! ## §2 — The fixpoint (unfolding) laws for the binders. -/

/-- **`mu_unfold` (PROVED)**: `denote (μ x. a) ρ = denote a (ρ[x ↦ denote (μ x. a) ρ])`. The defining
recursion of a least-fixpoint binder, from `OrderHom.map_lfp` through `denote_mu`. -/
theorem mu_unfold (x : Var) (a : Formula S) (ρ : Env S) :
    denote S (.mu x a) ρ
      = denote S a (Function.update ρ x (denote S (.mu x a) ρ)) := by
  conv_lhs => rw [denote_mu]
  conv_rhs => rw [denote_mu]
  exact (bodyHom S a ρ x).map_lfp.symm

/-- **`nu_unfold` (PROVED)**: `denote (ν x. a) ρ = denote a (ρ[x ↦ denote (ν x. a) ρ])`. From
`OrderHom.map_gfp`. -/
theorem nu_unfold (x : Var) (a : Formula S) (ρ : Env S) :
    denote S (.nu x a) ρ
      = denote S a (Function.update ρ x (denote S (.nu x a) ρ)) := by
  conv_lhs => rw [denote_nu]
  conv_rhs => rw [denote_nu]
  exact (bodyHom S a ρ x).map_gfp.symm

/-! ## §3 — The CTL ENCODING: every CTL operator IS the denotation of its standard μ/ν-formula.

This is the headline of the module: the semantic CTL of `Proof/CTL.lean` is recovered, on the nose, as
the syntactic μ-calculus. The non-fixpoint operators `EX`/`AX` are direct (`dia`/`box` of an atom). The
fixpoint operators reduce a `bodyHom` to the matching `CTL.*Body` by `OrderHom.ext` (the underlying
functions agree once `Function.update_self` collapses `ρ[0↦X] 0 = X` at the recursion variable), then
`congrArg .lfp`/`.gfp`. We bind the recursion variable to `0` throughout (the canonical fresh name). -/

/-- **`encode_EX` (PROVED)**: `EX P = denote (◇ (atom P))`. The existential modal next is the diamond
of an atom — no fixpoint. -/
theorem encode_EX (P : Set S.Config) (ρ : Env S) :
    denote S (.dia (.atom P)) ρ = EX S P := rfl

/-- **`encode_AX` (PROVED)**: `AX P = denote (□ (atom P))`. The universal modal next is the box of an
atom. -/
theorem encode_AX (P : Set S.Config) (ρ : Env S) :
    denote S (.box (.atom P)) ρ = AX S P := rfl

/-- The `bodyHom` of the `EU`-encoding formula equals `CTL.euBody S P Q` as an `OrderHom`. The
underlying functions agree: `denote (atom Q ∨ (atom P ∧ ◇(var 0))) (ρ[0↦X])`
`= Q ∪ (P ∩ pre S ((ρ[0↦X]) 0)) = Q ∪ (P ∩ pre S X)` by `Function.update_self`. -/
theorem euBody_eq (P Q : Set S.Config) (ρ : Env S) :
    bodyHom S (.or_ (.atom Q) (.and_ (.atom P) (.dia (.var 0)))) ρ 0 = euBody S P Q := by
  apply OrderHom.ext
  funext X
  show Q ∪ (P ∩ pre S ((Function.update ρ 0 X) 0)) = Q ∪ (P ∩ pre S X)
  rw [Function.update_self]

/-- **`encode_EU` (PROVED)**: `EU P Q = denote (μx. Q ∨ (P ∧ ◇x))`. The standard least-fixpoint
encoding of "along some path, `P` until `Q`". -/
theorem encode_EU (P Q : Set S.Config) (ρ : Env S) :
    denote S (.mu 0 (.or_ (.atom Q) (.and_ (.atom P) (.dia (.var 0))))) ρ = EU S P Q := by
  rw [denote_mu, euBody_eq]; rfl

/-- The `bodyHom` of the `AU`-encoding formula equals `CTL.auBody S P Q`. Same shape as `euBody_eq`
with `□` (`preAll`) in place of `◇` (`pre`). -/
theorem auBody_eq (P Q : Set S.Config) (ρ : Env S) :
    bodyHom S (.or_ (.atom Q) (.and_ (.atom P) (.box (.var 0)))) ρ 0 = auBody S P Q := by
  apply OrderHom.ext
  funext X
  show Q ∪ (P ∩ preAll S ((Function.update ρ 0 X) 0)) = Q ∪ (P ∩ preAll S X)
  rw [Function.update_self]

/-- **`encode_AU` (PROVED)**: `AU P Q = denote (μx. Q ∨ (P ∧ □x))`. The least-fixpoint encoding of
"along every path, `P` until `Q`". -/
theorem encode_AU (P Q : Set S.Config) (ρ : Env S) :
    denote S (.mu 0 (.or_ (.atom Q) (.and_ (.atom P) (.box (.var 0))))) ρ = AU S P Q := by
  rw [denote_mu, auBody_eq]; rfl

/-- **`encode_EF` (PROVED)**: `EF P = denote (μx. P ∨ ◇x)`. The textbook μ-formula for "`P` is
reachable along some path". Proved through `encode_EU` with `Q := P`, `P := univ` (since `EF = EU univ
P` and `univ ∧ ◇x = ◇x`), reducing the `bodyHom` directly. -/
theorem encode_EF (P : Set S.Config) (ρ : Env S) :
    denote S (.mu 0 (.or_ (.atom P) (.dia (.var 0)))) ρ = EF S P := by
  rw [denote_mu]
  -- show the body equals `euBody S univ P` (since `EF P = EU univ P = (euBody S univ P).lfp`).
  have hbody : bodyHom S (.or_ (.atom P) (.dia (.var 0))) ρ 0 = euBody S Set.univ P := by
    apply OrderHom.ext
    funext X
    show P ∪ pre S ((Function.update ρ 0 X) 0) = P ∪ (Set.univ ∩ pre S X)
    rw [Function.update_self, Set.univ_inter]
  rw [hbody]; rfl

/-- **`encode_AF` (PROVED)**: `AF P = denote (μx. P ∨ □x)`. The μ-formula for "on every path `P`
eventually holds" (operator-level; the liveness *reading* inherits `CTL.lean`'s fairness gate). -/
theorem encode_AF (P : Set S.Config) (ρ : Env S) :
    denote S (.mu 0 (.or_ (.atom P) (.box (.var 0)))) ρ = AF S P := by
  rw [denote_mu]
  have hbody : bodyHom S (.or_ (.atom P) (.box (.var 0))) ρ 0 = auBody S Set.univ P := by
    apply OrderHom.ext
    funext X
    show P ∪ preAll S ((Function.update ρ 0 X) 0) = P ∪ (Set.univ ∩ preAll S X)
    rw [Function.update_self, Set.univ_inter]
  rw [hbody]; rfl

/-- The `bodyHom` of the `EG`-encoding formula equals `CTL.egBody S P`. -/
theorem egBody_eq (P : Set S.Config) (ρ : Env S) :
    bodyHom S (.and_ (.atom P) (.dia (.var 0))) ρ 0 = egBody S P := by
  apply OrderHom.ext
  funext X
  show P ∩ pre S ((Function.update ρ 0 X) 0) = P ∩ pre S X
  rw [Function.update_self]

/-- **`encode_EG` (PROVED)**: `EG P = denote (νx. P ∧ ◇x)`. The greatest-fixpoint encoding of "along
some path `P` holds forever". -/
theorem encode_EG (P : Set S.Config) (ρ : Env S) :
    denote S (.nu 0 (.and_ (.atom P) (.dia (.var 0)))) ρ = EG S P := by
  rw [denote_nu, egBody_eq]; rfl

/-- The `bodyHom` of the `AG`-encoding formula equals `CTL.agBody S P`. -/
theorem agBody_eq (P : Set S.Config) (ρ : Env S) :
    bodyHom S (.and_ (.atom P) (.box (.var 0))) ρ 0 = agBody S P := by
  apply OrderHom.ext
  funext X
  show P ∩ preAll S ((Function.update ρ 0 X) 0) = P ∩ preAll S X
  rw [Function.update_self]

/-- **`encode_AG` (PROVED)**: `AG P = denote (νx. P ∧ □x)`. The greatest-fixpoint encoding of the
branching invariant "along every path `P` holds forever" — the headline ν-formula. -/
theorem encode_AG (P : Set S.Config) (ρ : Env S) :
    denote S (.nu 0 (.and_ (.atom P) (.box (.var 0)))) ρ = AG S P := by
  rw [denote_nu, agBody_eq]; rfl

/-! ## §4 — A worked fixpoint-ALTERNATION example + the TEETH (non-vacuity).

The encoding theorems above are the primary teeth — they prove the embedding is faithful (a vacuous
`denote` could never equal `EF`/`AG`). Here we make the μ/ν alternation CONCRETE on `CTL.branchSys`
(the `Fin 3` witness `0 → 1`, `0 → 2`, `1 ↺`, `2 ↺`), showing the least- and greatest-fixpoint formulae
genuinely separate: `0` is in `μx. {1} ∨ ◇x` but NOT in `νx. {1}ᶜ ∧ □x`. Both reuse the proved CTL
teeth (`mem_EF_branch`, `not_mem_AF_branch`) through the encoding. -/

/-- The `EF`-formula on the branching witness: `μx. {1} ∨ ◇x`, the syntactic form of `EF branchSys {1}`. -/
def efPhi : Formula CTL.branchSys :=
  .mu 0 (.or_ (.atom CTL.tgt) (.dia (.var 0)))

/-- The `AG`-of-complement formula: `νx. {1}ᶜ ∧ □x`, the syntactic form of `AG branchSys {1}ᶜ`. -/
def agComplPhi : Formula CTL.branchSys :=
  .nu 0 (.and_ (.atom CTL.tgtᶜ) (.box (.var 0)))

/-- The empty environment (every recursion variable ↦ ∅) — the binders close over it, so the choice is
immaterial to `efPhi`/`agComplPhi`, which have no free variables. -/
def ρ₀ : Env CTL.branchSys := fun _ => (∅ : Set (Fin 3))

/-- **`denote_efPhi_eq` (PROVED)**: the `EF`-formula denotes exactly `EF branchSys {1}` — the encoding
specialized to the witness. -/
theorem denote_efPhi_eq : denote CTL.branchSys efPhi ρ₀ = EF CTL.branchSys CTL.tgt := by
  unfold efPhi; exact encode_EF CTL.tgt ρ₀

/-- **`denote_agComplPhi_eq` (PROVED)**: the `AG`-of-complement formula denotes `AG branchSys {1}ᶜ`. -/
theorem denote_agComplPhi_eq :
    denote CTL.branchSys agComplPhi ρ₀ = AG CTL.branchSys CTL.tgtᶜ := by
  unfold agComplPhi; exact encode_AG CTL.tgtᶜ ρ₀

/-- **TEETH 1 — `mem_denote_efPhi` (PROVED)**: the root `0` IS in the μ-formula `μx. {1} ∨ ◇x`,
because `0 → 1` reaches `{1}` (reusing `CTL.mem_EF_branch` through the encoding). -/
theorem mem_denote_efPhi : (0 : Fin 3) ∈ denote CTL.branchSys efPhi ρ₀ := by
  rw [denote_efPhi_eq]; exact CTL.mem_EF_branch

/-- **TEETH 2 — `not_mem_denote_agComplPhi` (PROVED)**: the root `0` is NOT in the ν-formula
`νx. {1}ᶜ ∧ □x`. Were it, then (via `EF_EG_dual`: `EF {1} = (AG {1}ᶜ)ᶜ`) `0` would be OUTSIDE
`EF {1}` — contradicting TEETH 1. So swapping `μ`→`ν` and the polarity flips membership of `0`: the
fixpoint alternation is real, not collapsed. -/
theorem not_mem_denote_agComplPhi : (0 : Fin 3) ∉ denote CTL.branchSys agComplPhi ρ₀ := by
  rw [denote_agComplPhi_eq]
  intro hag
  -- `EF {1} = (AG {1}ᶜ)ᶜ`, so `0 ∈ AG {1}ᶜ` means `0 ∉ EF {1}`.
  have hnotEF : (0 : Fin 3) ∉ EF CTL.branchSys CTL.tgt := by
    rw [CTL.EF_EG_dual]; exact fun h => h hag
  exact hnotEF CTL.mem_EF_branch

/-- **TEETH 3 — `efPhi_ne_agComplPhi_denote` (PROVED): the μ/ν alternation genuinely separates.** The
two formulae denote DIFFERENT sets on the witness — `0` is in the μ-formula but not the ν-formula. A
direct refutation that the least-fixpoint `EF` and the (complemented) greatest-fixpoint `AG` collapse
into one another. The headline alternation teeth. -/
theorem efPhi_ne_agComplPhi_denote :
    denote CTL.branchSys efPhi ρ₀ ≠ denote CTL.branchSys agComplPhi ρ₀ := by
  intro h
  exact not_mem_denote_agComplPhi (h ▸ mem_denote_efPhi)

/-! ## §5 — Axiom-hygiene tripwires.

Every keystone is pinned to the kernel triple. `encode_EX`/`encode_AX` are `rfl`; the fixpoint encoders
and the unfolds rest on mathlib's `OrderHom.lfp`/`gfp` (whose `Classical.choice` enters via `sInf`/
`sSup` on `Set`, unavoidable and already present in `CTL.lean`/`Temporal.lean`). The alternation TEETH
go through `CTL.EF_EG_dual` (the genuinely-classical De Morgan dual) — they still pin within the
standard kernel triple `{propext, Classical.choice, Quot.sound}`, exactly as `CTL.EF_EG_dual` itself. -/

#assert_axioms denoteFun_mono
#assert_axioms denote_mu
#assert_axioms denote_nu
#assert_axioms mu_unfold
#assert_axioms nu_unfold
#assert_axioms encode_EX
#assert_axioms encode_AX
#assert_axioms encode_EU
#assert_axioms encode_AU
#assert_axioms encode_EF
#assert_axioms encode_AF
#assert_axioms encode_EG
#assert_axioms encode_AG
#assert_axioms mem_denote_efPhi
#assert_axioms not_mem_denote_agComplPhi
#assert_axioms efPhi_ne_agComplPhi_denote

-- Module-wide pin: EVERY theorem under the namespace stays within the standard kernel triple (catches
-- future drift). No `except` clause — even the alternation teeth (through `CTL.EF_EG_dual`) pin clean.
#assert_namespace_axioms Dregg2.Proof.MuCalculus

/-! ## It runs (`#eval`) — the fixpoint alternation, decided on the finite witness (non-vacuity).

`branchSys` is fully decidable, so the membership facts behind the alternation teeth are
`#eval`-checkable directly on the underlying step relation. -/

-- `0 ∈ EF {1}`: `0 → 1` reaches the target (the μ-formula's content) — true.
#eval decide (∃ t : Fin 3, CTL.branchStep 0 t ∧ t = (1 : Fin 3))
-- `0 ∉ AX {1}` ⇒ the ν-`□`-formula cannot keep `0` in `{1}ᶜ`-safety as `EF` does — the escape 0→1 is
-- precisely why `0` leaves `AG {1}ᶜ`: `0` has a successor (`1`) INSIDE `{1}`, i.e. outside `{1}ᶜ`.
#eval decide (∃ t : Fin 3, CTL.branchStep 0 t ∧ t = (1 : Fin 3))   -- the 0→1 witness, again — true

end Dregg2.Proof.MuCalculus
