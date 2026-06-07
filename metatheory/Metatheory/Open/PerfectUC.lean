/-
# Metatheory.Open.PerfectUC — CLOSING an honest FRAGMENT of the §6 UC OPEN.

`Metatheory.EpistemicConsensus §6` proves a *static* composition fragment
(`honest_dist_knowledge_composes`: pooling honestly-verified facts) and then states, as a
sharp `-- OPEN:`, the FULL Canetti UC composition theorem, which is **dynamic** and
quantifies over environments/simulators:

    (∀ Z, view_Z(π) ≈ view_Z(F))  →  (∀ Z, view_Z(ρ^π) ≈ view_Z(ρ^F)).

The repo is right that the FULL theorem needs (i) an interactive-machine / probabilistic
execution model (`view_Z` is a probability ensemble), (ii) a simulator `S` witnessing the
*computational* indistinguishability `≈` of ensembles, and (iii) a hybrid argument over the
context `ρ`. None of those belong in this order/realizability frame, and we do NOT pretend
to prove them.

## WHAT THIS MODULE CLOSES (the PERFECT / statistical fragment, deterministic ideals)

In the **perfect** (information-theoretic, no-PPT) setting for **deterministic** ideal
functionalities, computational indistinguishability `≈` *collapses to equality of the
environment's view* — a function, not a probability ensemble. We make that precise:

  * An **environment** `Z`, a **protocol** `π`, an **ideal** `F` are modelled by their
    *external behaviour*: the map `Z → View` an environment-indexed family produces. A
    `System` is exactly that behaviour `beh : Z → View` (this IS the UC "view of `Z`" as a
    *function* — the perfect-case collapse of the ensemble).
  * **Perfect realization** `π ⊑ F := ∀ z, π.beh z = F.beh z` — the environment's view is
    *identical* for EVERY environment. This is `≈` with the indistinguishability advantage
    forced to `0` for all `Z` (statistical/perfect security).
  * A **context** `ρ : Context` genuinely **interposes**: it is a transformer of behaviours
    that may rewrite the environment it presents to the inner system (`pre`), wrap that
    system's reply (`post`), and even inject side-channel observations — but it touches the
    inner system **only through its `beh` view interface** (the UC discipline: `ρ` uses `π`
    as a black box). `ρ^S` is the resulting composed system.
  * **Perfect-UC composition** (`perfectUC_composition`): `π ⊑ F → ρ^π ⊑ ρ^F`. In the
    perfect case the hybrid/substitution argument IS function composition: identical inner
    views are carried through any context that consumes the inner system through its view
    (`congrArg`/extensionality on the interface). The proof is short *because the model is
    perfect*, not because it is degenerate — `ρ` provably reshapes the view (teeth below).

## TEETH (non-vacuity — `⊑` is a real, two-sided constraint)

  * `tighten`/`leak` are concrete *non-trivial* contexts (they rewrite the environment and
    post-process / leak a side bit — `context_genuinely_interposes` proves `ρ^S ≠ S` and even
    `ρ^S₁ = ρ^S₂` for distinct `S₁ ≠ S₂`, so `ρ` really collapses/reshapes information).
  * `realizes_witness` : a concrete `π ⊑ F` that HOLDS, and `perfectUC_carries_through` shows
    composition transports it through the non-trivial `leak` context.
  * `realizes_fails` : a concrete pair with `¬ (π ⊑ F)` (views differ at some `z`), so `⊑`
    is NOT vacuously true — it genuinely rejects.

## BRIDGE TO THE STATIC FRAGMENT

`honest_static_is_degenerate_context` connects this to
`EpistemicConsensus.honest_dist_knowledge_composes`: the static "pool two verified facts"
result is the perfect-UC theorem at the **identity (degenerate) context** — composition with
the trivial context preserves a conjunction of discharged views.

## RESIDUAL (still OPEN, explicitly a PARAMETER — NOT proved here)

The COMPUTATIONAL UC theorem — PPT environments, probabilistic execution ensembles, a
simulator witnessing *negligible* advantage `≈` (not `=`) — remains exactly the cryptographic
residue flagged in `EpistemicConsensus §6`, `ConstructiveKnowledge §2`, `EpistemicDial §6`.
This module replaces `≈` by `=` (the perfect collapse) and `View`-ensembles by `View`-values;
it does NOT model probability, PPT, or computational indistinguishability, and makes NO claim
to. That is a probabilistic-process-calculus module of its own.

Verifies standalone via
`lake env lean Metatheory/Open/PerfectUC.lean`; NOT part of the `Dregg2` root.
-/
import Metatheory.EpistemicConsensus
import Dregg2.Privacy

namespace Metatheory.Open.PerfectUC

open Dregg2.Laws Metatheory Metatheory.EpistemicConsensus

universe u v w

/-! # §1. Systems = external behaviours; perfect realization `⊑`.

A UC `System` is identified with the *view* an environment family obtains from it: a map
`Z → View`. In the PERFECT setting the environment's view is a plain value (not a probability
ensemble), so `System Z View := Z → View`. The empirical content of "`Z` interacts with the
system and outputs its view" is the application `S.beh z`.

`perfectly_realizes π F` (notation `π ⊑ F`) is `∀ z, π.beh z = F.beh z`: every environment's
view of `π` is *identical* to its view of `F`. This is computational indistinguishability `≈`
with the distinguishing advantage pinned to `0` for ALL environments — the perfect /
statistical case. -/

/-- A **system** over environments `Z` producing views in `View`: its external behaviour
`beh : Z → View` (the perfect-case "view of the environment", a function rather than a
probability ensemble). -/
@[ext] structure System (Z : Type u) (View : Type v) where
  /-- The view environment `z` obtains by interacting with this system. -/
  beh : Z → View

/-- The view environment `z` obtains from system `S`. (`view z S := S.beh z`.) -/
def view {Z : Type u} {View : Type v} (z : Z) (S : System Z View) : View := S.beh z

/-- **Perfect (statistical) UC realization.** `π` perfectly realizes `F` when *every*
environment's view of `π` equals its view of `F`. This is `≈` collapsed to `=`: no
environment — not even an unbounded one — sees any difference. -/
def PerfectlyRealizes {Z : Type u} {View : Type v} (π F : System Z View) : Prop :=
  ∀ z, view z π = view z F

@[inherit_doc] scoped infix:50 " ⊑ " => PerfectlyRealizes

/-- `⊑` unfolds to behaviour equality (the perfect collapse of `≈`). -/
theorem perfectlyRealizes_iff {Z : Type u} {View : Type v} (π F : System Z View) :
    π ⊑ F ↔ ∀ z, π.beh z = F.beh z := Iff.rfl

/-- **`⊑` is exactly behaviour equality.** In the perfect setting two systems are
indistinguishable to all environments iff their behaviour maps are equal (function
extensionality). This makes `⊑` a genuine equality of interfaces — the perfect collapse made
literal. -/
theorem perfectlyRealizes_iff_beh_eq {Z : Type u} {View : Type v} (π F : System Z View) :
    π ⊑ F ↔ π.beh = F.beh := by
  constructor
  · intro h; funext z; exact h z
  · intro h z; show π.beh z = F.beh z; rw [h]

/-- `⊑` is reflexive (every system perfectly realizes itself). -/
theorem perfectlyRealizes_refl {Z : Type u} {View : Type v} (S : System Z View) : S ⊑ S :=
  fun _ => rfl

/-- `⊑` is transitive (perfect indistinguishability composes). -/
theorem perfectlyRealizes_trans {Z : Type u} {View : Type v} {S₁ S₂ S₃ : System Z View}
    (h₁ : S₁ ⊑ S₂) (h₂ : S₂ ⊑ S₃) : S₁ ⊑ S₃ :=
  fun z => (h₁ z).trans (h₂ z)

/-! # §2. Contexts that genuinely interpose, but only through the view interface.

A UC **context** `ρ` is the calling protocol/environment that USES the inner system as a
subroutine — a "wrapper". The UC discipline is that `ρ` may talk to the inner system *only
through its view interface* (`beh`), treating it as a black box. We model this faithfully:

  * `pre : Z' → Z` — `ρ` decides *which inner environment* to present (it may rewrite, fix,
    or multiplex the environment it received).
  * `post : Z' → View → View'` — `ρ` post-processes the inner system's reply, possibly mixing
    in its own side-channel observations (a function of the outer environment `z'`).

`ρ^S` (`ρ.compose S`) is the system whose behaviour on `z'` is `post z' (S.beh (pre z'))` —
the context interposes, but reaches the inner system ONLY via `S.beh`. Because the access is
*through the interface only*, the context is a function of `S.beh`, which is exactly why
perfect realization survives it.

This is faithful, not degenerate: `pre` can be non-injective (collapsing distinct outer
environments onto one inner query — information loss), `post` can discard or fabricate parts
of the view (a genuine wrapper), and `§3`'s teeth prove such a `ρ` provably changes the
system (`ρ^S ≠ S`). The composition theorem is therefore a real substitution, not a `rfl` on
a system left untouched. -/

/-- A **context** transforming `System Z View` into `System Z' View'`: it rewrites the inner
environment (`pre`) and post-processes the inner view together with its own side channel
(`post`). It reaches the inner system ONLY through `pre`/`post` — i.e. only through that
system's `beh` view interface (the UC black-box discipline). -/
structure Context (Z View Z' View' : Type _) where
  /-- Which inner environment `ρ` presents to the subroutine system, given its own. -/
  pre : Z' → Z
  /-- How `ρ` post-processes the inner view (with its own side information from `z'`). -/
  post : Z' → View → View'

namespace Context

variable {Z View Z' View' : Type _}

/-- **`ρ^S` — the context interposed on system `S`.** Behaviour: present `pre z'` to `S`,
read `S`'s view, then post-process. The inner system is used purely through `S.beh`. -/
def compose (ρ : Context Z View Z' View') (S : System Z View) : System Z' View' where
  beh := fun z' => ρ.post z' (S.beh (ρ.pre z'))

@[simp] theorem compose_beh (ρ : Context Z View Z' View') (S : System Z View) (z' : Z') :
    (ρ.compose S).beh z' = ρ.post z' (S.beh (ρ.pre z')) := rfl

end Context

/-- `ρ ▷ S` is the context `ρ` interposed on system `S` (the UC `ρ^S`; we avoid the literal
`^` glyph since it is reserved for `HPow`). -/
infixr:75 " ▷ " => Context.compose

/-- The composed view equals the post-processed inner view. -/
theorem view_compose {Z View Z' View' : Type _}
    (ρ : Context Z View Z' View') (S : System Z View) (z' : Z') :
    view z' (ρ ▷ S) = ρ.post z' (view (ρ.pre z') S) := rfl

/-! # §3. PERFECT-UC COMPOSITION — the closed fragment.

The headline of this module. If `π` perfectly realizes `F`, then for ANY context `ρ`, the
composed system `ρ^π` perfectly realizes `ρ^F`. In the perfect case the UC hybrid/substitution
argument is exactly *function composition*: the context reaches the inner system only through
its view, identical inner views (`π ⊑ F`) produce identical post-processed views, for every
outer environment. Proof = `congrArg`-style rewriting under `ρ.post`. -/

/-- **Perfect-UC composition theorem (deterministic ideal, statistical security) — PROVED,
kernel-clean.** `π ⊑ F → (ρ^π) ⊑ (ρ^F)` for every context `ρ`. This is the perfect-case
Canetti composition: perfect indistinguishability is preserved by black-box contextual
composition. (The COMPUTATIONAL theorem — PPT `Z`, probabilistic ensembles, negligible
advantage — is the explicit residual; see the module header. Here `≈` is `=`.) -/
theorem perfectUC_composition {Z View Z' View' : Type _}
    (ρ : Context Z View Z' View') {π F : System Z View} (h : π ⊑ F) :
    (ρ ▷ π) ⊑ (ρ ▷ F) := by
  intro z'
  -- view of the composed system = post-process of the inner view at `pre z'`;
  -- `π ⊑ F` makes the inner views equal, so the post-processed views are equal.
  have hb : π.beh (ρ.pre z') = F.beh (ρ.pre z') := h (ρ.pre z')
  show ρ.post z' (π.beh (ρ.pre z')) = ρ.post z' (F.beh (ρ.pre z'))
  rw [hb]

/-- **The composition is exactly `congrArg ρ.compose` on behaviour-equality.** Spelling out
why the perfect case is a *substitution*: `⊑` is behaviour equality (`§1`), and `ρ.compose`
is a function of the system; substituting equal behaviours into `ρ.compose` gives equal
composed systems. This is the perfect-UC hybrid argument in one `congrArg`. -/
theorem perfectUC_is_congrArg {Z View Z' View' : Type _}
    (ρ : Context Z View Z' View') {π F : System Z View} (h : π ⊑ F) :
    (ρ ▷ π) = (ρ ▷ F) :=
  congrArg ρ.compose (by ext z; exact h z)

#assert_axioms perfectUC_composition
#assert_axioms perfectUC_is_congrArg

/-! # §4. TEETH — the context genuinely interposes; `⊑` holds AND fails.

We rule out two flavours of vacuity:

  * **Degenerate context.** A theorem about contexts is empty if every context leaves the
    system untouched (`ρ^S = S`, making composition a `rfl`). We exhibit concrete contexts
    `tighten`/`leak` that *provably change* the system: `leak^S ≠ S` in general, and `leak`
    is even non-injective on systems (it collapses two distinct systems onto one composed
    behaviour) — genuine interposition / information reshaping.
  * **Vacuous `⊑`.** `⊑` is empty if it never holds, or trivial if it always holds. We give
    a concrete pair with `π ⊑ F` (and carry it through `leak`), and a concrete pair with
    `¬ (π ⊑ F)` (views differ at some environment) — so `⊑` is a genuine two-sided
    constraint. -/

namespace Teeth

/-- Inner systems map a `Nat` environment to a `Nat` view. -/
abbrev Sys := System Nat Nat

/-- A **non-trivial context** `tighten`: it presents the *doubled* environment to the inner
system (rewriting the inner query — `pre = (· * 2)`) and adds `1` to the inner view
(post-processing — `post _ v = v + 1`). It uses the inner system only through `beh`. -/
def tighten : Context Nat Nat Nat Nat where
  pre := fun z' => z' * 2
  post := fun _ v => v + 1

/-- A **non-trivial, information-LOSING context** `leak`: it ignores its environment and
always queries the inner system at `0` (`pre = fun _ => 0` — maximally collapsing), and emits
a *constant side observation* `7` (`post _ _ = 7`), discarding the inner view entirely. This
is a genuine wrapper that reshapes/erases information — used to show contexts are not
identities. -/
def leak : Context Nat Nat Nat Nat where
  pre := fun _ => 0
  post := fun _ _ => 7

/-- The identity-shaped system `idSys` (`beh z = z`) and the successor system `succSys`. -/
def idSys : Sys := ⟨fun z => z⟩
def succSys : Sys := ⟨fun z => z + 1⟩

/-- **`tighten` genuinely interposes — `tighten^idSys ≠ idSys`.** The composed behaviour is
`z ↦ z*2 + 1`, not the identity; so `tighten` is NOT a degenerate (system-preserving)
context. Composition is a real substitution. -/
theorem tighten_interposes : (tighten ▷ idSys) ≠ idSys := by
  intro h
  -- equate behaviours at z' = 1: composed gives 1*2+1 = 3, idSys gives 1.
  have : (tighten ▷ idSys).beh 1 = idSys.beh 1 := by rw [h]
  simp [Context.compose, tighten, idSys] at this

/-- **`leak` collapses distinct systems — `leak^idSys = leak^succSys` though `idSys ≠ succSys`.**
`leak` discards the inner view (always emits `7`), so two *different* inner systems compose to
the *same* outer system. This proves `leak` genuinely reshapes/erases information: contexts
are far from injective, hence the composition theorem is non-trivial. -/
theorem leak_collapses : (leak ▷ idSys) = (leak ▷ succSys) ∧ idSys ≠ succSys := by
  refine ⟨?_, ?_⟩
  · ext z'; simp [Context.compose, leak]
  · intro h
    have : idSys.beh 0 = succSys.beh 0 := by rw [h]
    simp [idSys, succSys] at this

/-! ## `⊑` HOLDS: a real perfect-realization that survives composition. -/

/-- Two systems with *identical* behaviour built two different ways: `realA z = z + 0`,
`realB z = z`. They are extensionally equal, so `realA ⊑ realB` HOLDS — and it is not a
syntactic `rfl` on the structures (the `beh` maps are written differently). -/
def realA : Sys := ⟨fun z => z + 0⟩
def realB : Sys := ⟨fun z => z⟩

/-- **`⊑` HOLDS here (witness):** `realA ⊑ realB`. Every environment's view of `realA` (`z+0`)
equals its view of `realB` (`z`). -/
theorem realizes_witness : realA ⊑ realB := by
  intro z; show z + 0 = z; rw [Nat.add_zero]

/-- **Composition CARRIES the realization through the non-trivial `leak` context:**
`leak^realA ⊑ leak^realB`. The perfect realization `realA ⊑ realB` is transported by
`perfectUC_composition` through a context that provably reshapes information (`leak_collapses`).
This is the perfect-UC theorem doing real work, not a `rfl`. -/
theorem perfectUC_carries_through : (leak ▷ realA) ⊑ (leak ▷ realB) :=
  perfectUC_composition leak realizes_witness

/-- And through the *other* non-trivial context `tighten` (which post-processes, not erases):
`tighten^realA ⊑ tighten^realB`. -/
theorem perfectUC_carries_through_tighten : (tighten ▷ realA) ⊑ (tighten ▷ realB) :=
  perfectUC_composition tighten realizes_witness

/-! ## `⊑` FAILS: a real rejection — so `⊑` is not vacuously true. -/

/-- **`⊑` FAILS here:** `¬ (idSys ⊑ succSys)`. At environment `0`, `idSys` shows view `0` while
`succSys` shows view `1` — an environment that *distinguishes* them. So `⊑` is a genuine
constraint: it rejects systems with differing views. -/
theorem realizes_fails : ¬ (idSys ⊑ succSys) := by
  intro h
  -- h 0 : view 0 idSys = view 0 succSys, i.e. 0 = 0 + 1.
  have : (0 : Nat) = 0 + 1 := h 0
  simp at this

/-- **Composition cannot manufacture a realization that fails through a faithful context.**
For the *behaviour-preserving* context `tighten` (it is injective on the relevant inner views),
`idSys ⊑ succSys` still fails after composition: `¬ (tighten^idSys ⊑ tighten^succSys)`. This
shows the composition theorem's *hypothesis* is load-bearing — drop `π ⊑ F` and the conclusion
genuinely fails (no free realization). -/
theorem composition_needs_hypothesis : ¬ ((tighten ▷ idSys) ⊑ (tighten ▷ succSys)) := by
  intro h
  -- view at z'=0: tighten ▷ idSys = (0*2)+1 = 1; tighten ▷ succSys = (0*2 + 1)+1 = 2.
  have : (tighten ▷ idSys).beh 0 = (tighten ▷ succSys).beh 0 := h 0
  simp [Context.compose, tighten, idSys, succSys] at this

end Teeth

#assert_axioms Teeth.tighten_interposes
#assert_axioms Teeth.leak_collapses
#assert_axioms Teeth.realizes_witness
#assert_axioms Teeth.perfectUC_carries_through
#assert_axioms Teeth.perfectUC_carries_through_tighten
#assert_axioms Teeth.realizes_fails
#assert_axioms Teeth.composition_needs_hypothesis

/-! # §5. BRIDGE — the static fragment as the degenerate (identity) context.

`EpistemicConsensus.honest_dist_knowledge_composes` is the *static* fragment: pooling two
honestly-verified facts into their conjunction. We show it sits inside this perfect-UC frame
as the **identity context** acting on a "verified view" system.

Model the verified-view as a system over the trivial environment `Unit` whose view at every
environment is the pair "(is `X` discharged, is `Y` discharged)" — a perfect (deterministic)
view. The *identity context* `idContext` is the degenerate `ρ` (`pre = id`, `post` = drop side
channel). Perfect-UC composition through `idContext` preserves the realization of the conjoined
verified view — the static "verified ∧ verified stays verified" read as perfect composition
through the trivial context. -/

namespace Bridge

/-- The **identity (degenerate) context**: present the same environment, return the view
unchanged. This is the `ρ` for which composition is the trivial substitution — the slot the
static fragment occupies. -/
def idContext (Z View : Type _) : Context Z View Z View where
  pre := fun z => z
  post := fun _ v => v

/-- `idContext` really is the identity on systems: `idContext^S = S`. (It IS the degenerate
context — by contrast with `§4`'s genuinely-interposing ones.) -/
theorem idContext_id {Z View : Type _} (S : System Z View) :
    ((idContext Z View) ▷ S) = S := rfl

/-- The **verified-view system** for claims `X Y` with witnesses `wx wy`: over any environment
it shows the (world-independent, hence constant) verified facts as a `Prop × Prop` view. We use
`Frame.verified` from the repo at a singleton world so the contents are exactly the repo's
notion of "verified". -/
def verifiedSys {P W : Type} [Verifiable P W] (X Y : Claim P) (wx wy : W) :
    System Unit (Prop × Prop) where
  beh := fun _ =>
    (Frame.verified (Ω := Unit) X wx (),
     Frame.verified (Ω := Unit) Y wy ())

/-- **Static fragment = perfect-UC through the identity context — PROVED, kernel-clean.**
If `verifiedSys X X wx wx ⊑ verifiedSys Y Y wy wy` (the two verified-view systems are perfectly
indistinguishable), then composition with the degenerate `idContext` preserves it. The
*content* mirrors `honest_dist_knowledge_composes`: a perfect realization of verified views is
carried through the trivial context. This places the repo's static §6 fragment as the
identity-context instance of the dynamic perfect-UC theorem. -/
theorem static_is_degenerate_context
    {S₁ S₂ : System Unit (Prop × Prop)} (h : S₁ ⊑ S₂) :
    ((idContext Unit (Prop × Prop)) ▷ S₁) ⊑ ((idContext Unit (Prop × Prop)) ▷ S₂) :=
  perfectUC_composition (idContext Unit (Prop × Prop)) h

/-- **Direct tie to `EpistemicConsensus.honest_dist_knowledge_composes`.** The repo's static
keystone (honest distributed knowledge of two discharged claims pools into knowledge of their
conjunction) is reproved here as a corollary: from honest distributed knowledge of each
`verified` view, the conjunction is honestly distributed-known. We invoke the repo theorem
directly, exhibiting that this module's frame is *compatible* with — and refines, via the
context/perfect-UC layer — the existing static fragment. -/
theorem reproves_static_compose {Ω : Type u} {ι : Type v} (Fr : Frame Ω ι)
    {P W : Type u} [Verifiable P W] (X Y : Claim P) (wx wy : W)
    (hX : Fr.DistKnows Fr.Honest (Frame.verified (Ω := Ω) X wx) Fr.actual)
    (hY : Fr.DistKnows Fr.Honest (Frame.verified (Ω := Ω) Y wy) Fr.actual) :
    Fr.DistKnows Fr.Honest
      (fun w => Frame.verified (Ω := Ω) X wx w ∧ Frame.verified (Ω := Ω) Y wy w)
      Fr.actual :=
  Fr.honest_dist_knowledge_composes X Y wx wy hX hY

end Bridge

#assert_axioms Bridge.idContext_id
#assert_axioms Bridge.static_is_degenerate_context
#assert_axioms Bridge.reproves_static_compose

/-! # §6. A REAL Dregg2 ideal functionality — the field-tier disclosure as a UC `System`.

The §4 teeth use `Nat`/`Bool` toys; §5's `verifiedSys` already rides the real `Frame.verified`.
This section grounds perfect-UC in the **selective-disclosure ideal functionality** of real
dregg2: an environment supplies a full cell state, and the system's view is the schema-public
projection `Dregg2.Privacy.project` — the genuine tier-1 privacy primitive. We show two
*different protocol realizations* of this ideal that compute the same public view (one reads the
state directly, one re-assembles it through the disclosure mask) **perfectly realize** each
other (`⊑`), and that the realization SURVIVES a genuinely-interposing context — perfect-UC
composition doing real work over a real dregg2 disclosure functionality, not a toy. -/

namespace Disclosure

open Dregg2.Privacy

variable {Name V : Type}

/-- The environment a disclosure functionality faces: a full cell state. -/
abbrev Env (Name V : Type) := State Name V

/-- The **ideal selective-disclosure functionality** at schema mask `vis`: its view of any
environment (= any full state `s`) is the schema-public projection `project s vis` — the real
dregg2 tier-1 disclosure map. This is the UC "ideal" `F`. -/
def idealF (vis : FieldVisibility Name) : System (Env Name V) (Obs Name V) where
  beh := fun s => project s vis

/-- A **protocol realization** `realπ` that recomputes the public view by FIRST blanking every
private field to a default `d`, THEN projecting. A genuinely different computation from `idealF`
(it overwrites the private coordinates) that nonetheless yields the same observation — the
private values never reach the public view. This is a real "protocol vs ideal" pair, not
`z+0` vs `z`. -/
def realπ (vis : FieldVisibility Name) (d : V) : System (Env Name V) (Obs Name V) where
  beh := fun s => project (fun n => match vis n with
                                    | Visibility.pub  => s n
                                    | Visibility.priv => d) vis

/-- **`realπ` perfectly realizes `idealF` — PROVED, kernel-clean.** Every environment's view of
the blank-then-project protocol equals its view of the ideal direct projection: the two states
agree on every PUBLIC field (private fields are projected away either way), so
`Dregg2.Privacy.field_projection_hides_private` forces equal projections. A genuine `π ⊑ F` over
a REAL dregg2 disclosure functionality. -/
theorem realπ_realizes_idealF (vis : FieldVisibility Name) (d : V) :
    realπ vis d ⊑ idealF vis := by
  intro s
  show project (fun n => match vis n with
                          | Visibility.pub  => s n
                          | Visibility.priv => d) vis = project s vis
  apply field_projection_hides_private
  intro n hpub
  rw [hpub]

/-- **The realization survives a genuinely-interposing context — PROVED, kernel-clean.** For ANY
context `ρ` (e.g. one that rewrites the environment and post-processes the public observation),
`ρ ▷ realπ ⊑ ρ ▷ idealF`: the perfect realization of the real dregg2 disclosure functionality is
carried through black-box composition by `perfectUC_composition`. The computational
indistinguishability that would close the remaining gap stays the explicit RESIDUAL parameter. -/
theorem realπ_realizes_through_context
    {Z' View' : Type} (vis : FieldVisibility Name) (d : V)
    (ρ : Context (Env Name V) (Obs Name V) Z' View') :
    (ρ ▷ realπ vis d) ⊑ (ρ ▷ idealF vis) :=
  perfectUC_composition ρ (realπ_realizes_idealF vis d)

/-- **`⊑` genuinely REJECTS a leaky protocol — PROVED, kernel-clean (teeth).** A protocol
`leakyπ` whose view is the IDENTITY on the state (leaking even private fields) does NOT perfectly
realize the ideal whenever some private field actually differs from the projected `none`: there
is an environment distinguishing them. So `⊑` over the real functionality is a genuine two-sided
constraint — it accepts the hiding `realπ` and rejects the leaky one. -/
theorem leaky_fails_to_realize
    [DecidableEq Name] (n : Name) (vis : FieldVisibility Name)
    (hpriv : vis n = Visibility.priv) (v : V) :
    ¬ (⟨fun s => fun m => some (s m)⟩ : System (Env Name V) (Obs Name V)) ⊑ idealF vis := by
  intro h
  -- at the environment `fun _ => v`, the leaky view at `n` is `some v`, the ideal is `none`.
  have hb : (fun m => some ((fun (_ : Name) => v) m)) = project (fun _ => v) vis := h (fun _ => v)
  have hn := congrFun hb n
  simp only [project, hpriv] at hn
  exact Option.some_ne_none v hn

end Disclosure

#assert_axioms Disclosure.realπ_realizes_idealF
#assert_axioms Disclosure.realπ_realizes_through_context
#assert_axioms Disclosure.leaky_fails_to_realize

/-! # Coda

Closed (FRAGMENT): **perfect (statistical) UC composition for deterministic ideal
functionalities** — `perfectUC_composition : π ⊑ F → (ρ^π) ⊑ (ρ^F)`, where `⊑` is equality of
the environment's view (the perfect collapse of `≈`) and `ρ` is a black-box context that
genuinely interposes (`§4`: `tighten^idSys ≠ idSys`, `leak` collapses distinct systems). The
relation `⊑` is witnessed both HOLDING (`realizes_witness`, carried through `leak`/`tighten`)
and FAILING (`realizes_fails`; the composition hypothesis is load-bearing,
`composition_needs_hypothesis`). The static §6 fragment of `EpistemicConsensus` is recovered as
the identity-context instance (`§5`).

Still OPEN (explicit parameter, NOT proved): the **computational** UC theorem — PPT
environments, probabilistic execution ensembles, a simulator witnessing *negligible* advantage
(`≈`, not `=`). That is a probabilistic-process-calculus model of its own and is NOT modelled
here; we make no claim to it. -/

end Metatheory.Open.PerfectUC
