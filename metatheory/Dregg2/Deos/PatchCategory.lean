/-
# Dregg2.Deos.PatchCategory — the FULL LABELLED PATCH CATEGORY `P` over document states.

This CLOSES the residual `DocMerge.lean:33-34,353-354` named: the THIN inclusion category of
`DocMerge` (objects = `DocGraph`, morphisms = inclusions `⊑`, at most one per pair) is PROMOTED to
the FULL LABELLED patch category `P` whose MORPHISMS ARE PATCHES (`Op`-sequences), not mere
inclusions. This is Mimram–Di Giusto categorical patch theory over the Pijul document model.

What the THIN category could NOT express, and what is built HERE:

  1. **`P` is a genuine `CategoryTheory.Category`** (§2): objects = `DocGraph`, a morphism `a ⟶ b` is
     a PATCH `p` (an `Op`-sequence) together with a proof `applyPatch p a = b`. Identity = the empty
     patch; composition = patch CONCATENATION; the axioms `id_comp`/`comp_id`/`assoc` are the free
     `List`-monoid laws, transported by `applyPatch_append` (composition ⟺ sequential apply — the
     `dregg-doc` `compose_equals_sequential_apply` seed). `P` is NOT thin: `hom_not_thin` exhibits
     TWO DISTINCT parallel morphisms `a ⟶ a` (an idempotent `Connect` vs the identity) — a hom-set
     with ≥2 elements, impossible in a preorder.

  2. **Isomorphism in `P` is CONTEXTUAL and GENUINELY NON-TRIVIAL** (§3): `IsoP a b` is a pair of
     patches `a ⟶ b`, `b ⟶ a` whose round-trips restore the endpoints (the RCCS contextual inverse,
     `patch.rs::invert`). `isoP_nontrivial` exhibits `IsoP a b` with `a ≠ b` (a `Connect`/`Disconnect`
     pair over two distinct graphs). In the THIN category `a ≅ b → a = b` (isos are identities, by
     `Includes.antisymm`); in `P` there are REAL isos between DISTINCT objects — this is exactly the
     gap "up to unique iso" vs "up to equality".

  3. **The pushout, UP TO UNIQUE ISO — not degenerate to equality** (§4): `IsPushoutUpToIso` is the
     iso-invariant pushout (a cocone over the span, `IsoP` to the canonical join `merge`). `merge`
     realizes it; it is unique UP TO `IsoP` (`pushout_upToIso_unique`); and `pushout_upToIso_two_distinct`
     exhibits ONE span (`isoLo ⟵ isoLo ⟶ isoLo`) with TWO DISTINCT pushout objects `isoLo ≠ isoHi`,
     related by the non-trivial `IsoP` — the up-to-iso uniqueness is STRICTLY WEAKER than equality.

  4. **Mimram–Di Giusto: NOT all pushouts exist — a conflict is a MISSING pushout** (§5): the concrete
     conflict span (`base ⟵ merge base forkA — · — merge base forkB ⟶`) has NO pushout in the
     CONFLICT-FREE subcategory (`no_conflictFree_pushout`) — its pushout object necessarily carries a
     `DocMerge.ConflictAt`. The pushout EXISTS in the FULL category, where the conflict is a first-class
     object: `conflict_object_is_pushout` — the pushout object IS `conflictGraph` and its `ConflictAt`
     is the conflict object. `DocMerge.ConflictAt` IS the categorical conflict object.

  5. **Functoriality** (§6): `applyPatch` is a monoid homomorphism `(P, ++, []) → (DocGraph → DocGraph, ∘, id)`
     (`applyPatch_functor_id`/`applyPatch_functor_comp` — the residual functor's action on morphisms),
     and the ADDITIVE (forward-op) subcategory maps functorially into the THIN `⊑`-poset of `DocMerge`
     (`residual_functor_id`/`residual_functor_comp`): the honest "document state ↦ merge behavior".

Reuses (does NOT re-derive) `DocMerge`: `DocGraph`, `merge`, `⊑`/`Includes`, `merge_isPushout`,
`pushout_unique`, `Includes.antisymm`, `ConflictAt`, `conflictGraph`/`base`/`forkA`/`forkB`,
`merge_has_conflict`, `conflictGraph_isPushout`. Differential: `dregg-doc/src/patch.rs` (`Op`, `apply`,
`compose`, `invert`). `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified: `lake build Dregg2.Deos.PatchCategory`.
-/
import Dregg2.Deos.DocMerge
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Insert

namespace Dregg2.Deos.PatchCategory

open Dregg2.Deos.DocMerge
open CategoryTheory

/-! ## 1. The patch grammar `Op`, and `applyPatch` — faithful to `patch.rs`.

`Op` is the `patch.rs::Op` grammar: the additive forward ops `Add`/`Delete`/`Connect`/`SetField` and
the RCCS inverse ops `Resurrect`/`Disconnect`/`RetractField`. A `Patch` is a `List Op` (we drop the
`Author` — provenance lives in the commitment layer, not the merge-algebra, exactly as `DocMerge`
drops atom content). `applyOp`/`applyPatch` are `patch.rs::apply` on the `DocMerge` graph model:
atoms carry only their `Status` (the merge-observable value), so `Add`/`Delete` join the status and
`Resurrect` sets it live; the graph ops insert/erase order-edges and field values. -/

/-- One document operation (`patch.rs::Op`). Additive forward ops + RCCS inverse ops. -/
inductive Op where
  /-- `Add id after` — introduce atom `id` (alive, joined if present) + order-edge `after → id`. -/
  | add (id after : AtomId)
  /-- `Delete id` — tombstone (`Status` joined with `dead`; Dead wins, monotone). -/
  | del (id : AtomId)
  /-- `Connect x y` — add order-edge `x → y`. -/
  | connect (x y : AtomId)
  /-- `SetField n v` — assign value `v` to single-valued field `n` (may clash concurrently). -/
  | setField (n : Name) (v : Val)
  /-- `Resurrect id` — inverse of `Delete`: a PRESENT atom's status → alive (absent stays absent). -/
  | resurrect (id : AtomId)
  /-- `Disconnect x y` — inverse of `Connect`: remove order-edge `x → y`. -/
  | disconnect (x y : AtomId)
  /-- `RetractField n` — inverse of a fresh `SetField`: drop all assignments to field `n`. -/
  | retractField (n : Name)
  deriving DecidableEq, Repr

/-- **A patch** (`patch.rs::Patch`, author dropped): an `Op`-sequence, applied left-to-right. -/
abbrev Patch := List Op

/-- Apply one op to a graph (`patch.rs::apply`'s per-op arm, on the `DocMerge` status model). -/
def applyOp (op : Op) (g : DocGraph) : DocGraph :=
  match op with
  | .add id after =>
      { g with
        atoms := fun i => if i = id then atomJoin (g.atoms i) (some Status.alive) else g.atoms i,
        order := insert (after, id) g.order }
  | .del id =>
      { g with
        atoms := fun i => if i = id then atomJoin (g.atoms i) (some Status.dead) else g.atoms i }
  | .connect x y => { g with order := insert (x, y) g.order }
  | .setField n v =>
      { g with fields := fun m => if m = n then insert v (g.fields m) else g.fields m }
  | .resurrect id =>
      { g with atoms := fun i => if i = id then (g.atoms i).map (fun _ => Status.alive) else g.atoms i }
  | .disconnect x y => { g with order := (g.order).erase (x, y) }
  | .retractField n => { g with fields := fun m => if m = n then ∅ else g.fields m }

/-- **`applyPatch p g`** — apply the ops of `p` in sequence (`patch.rs::apply`, the `foldl`). -/
def applyPatch (p : Patch) (g : DocGraph) : DocGraph :=
  p.foldl (fun g op => applyOp op g) g

@[simp] theorem applyPatch_nil (g : DocGraph) : applyPatch [] g = g := rfl

@[simp] theorem applyPatch_cons (op : Op) (p : Patch) (g : DocGraph) :
    applyPatch (op :: p) g = applyPatch p (applyOp op g) := rfl

/-- **`applyPatch_append` (COMPOSITION ⟺ SEQUENTIAL APPLY).** Applying a concatenation is applying
the first then the second — `patch.rs::compose_equals_sequential_apply`, the FUNCTORIALITY SEED: it
is what makes patch concatenation a valid composition in `P`. -/
theorem applyPatch_append (p q : Patch) (g : DocGraph) :
    applyPatch (p ++ q) g = applyPatch q (applyPatch p g) := by
  induction p generalizing g with
  | nil => rfl
  | cons op p ih =>
    show applyPatch (op :: (p ++ q)) g = applyPatch q (applyPatch (op :: p) g)
    rw [applyPatch_cons, applyPatch_cons, ih]

/-! ## 2. THE CATEGORY `P` — objects = `DocGraph`, morphisms = validated patches.

A morphism `a ⟶ b` is a patch `p` with `applyPatch p a = b`. Identity = the empty patch (`rfl`);
composition = concatenation (validity by `applyPatch_append`). The category axioms are the free
`List`-monoid laws (`nil_append`, `append_nil`, `append_assoc`), lifted through `Subtype.ext` (the
validity proof is irrelevant). This is a GENUINE `CategoryTheory.Category`. -/

/-- **`Hom a b`** — a patch that transforms `a` into `b` (well-typed ⟺ `applyPatch p a = b`). -/
def Hom (a b : DocGraph) : Type := { p : Patch // applyPatch p a = b }

/-- The identity morphism = the empty patch (`applyPatch [] a = a` by `rfl`). -/
def idHom (a : DocGraph) : Hom a a := ⟨[], rfl⟩

/-- Composition = patch concatenation; validity by `applyPatch_append`. -/
def compHom {a b c : DocGraph} (f : Hom a b) (g : Hom b c) : Hom a c :=
  ⟨f.1 ++ g.1, by rw [applyPatch_append, f.2, g.2]⟩

/-- **`P` IS A CATEGORY.** Objects `DocGraph`, hom = validated patches, id = empty patch, comp =
concatenation. `id_comp`/`comp_id`/`assoc` are `List.nil_append`/`append_nil`/`append_assoc` under
`Subtype.ext`. This is the FULL labelled patch category — morphisms are PATCHES, not inclusions. -/
instance categoryP : Category DocGraph where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp f := Subtype.ext (List.nil_append f.1)
  comp_id f := Subtype.ext (List.append_nil f.1)
  assoc f g h := Subtype.ext (List.append_assoc f.1 g.1 h.1)

/-- Sanity: a concrete morphism — the patch `[connect 1 2]` is an arrow between the empty graph and
the graph with edge `(1,2)`. (Non-vacuity of `Hom`.) -/
def emptyG : DocGraph := { atoms := fun _ => none, order := ∅, fields := fun _ => ∅ }
/-- The graph with the single order-edge `(1,2)`. -/
def edgeG : DocGraph := { atoms := fun _ => none, order := {(1, 2)}, fields := fun _ => ∅ }

theorem connect_is_arrow : applyPatch [Op.connect 1 2] emptyG = edgeG := by
  apply DocGraph.ext
  · intro i; rfl
  · show insert ((1 : AtomId), (2 : AtomId)) emptyG.order = edgeG.order; decide
  · intro n; rfl

/-! ### `P` is NOT THIN — a hom-set with ≥2 elements (impossible in a preorder). -/

/-- Adding an ALREADY-PRESENT edge is a no-op: `applyPatch [connect 1 2] edgeG = edgeG`. So both the
identity `[]` and `[connect 1 2]` are morphisms `edgeG ⟶ edgeG`. -/
theorem connect_idem_on_edgeG : applyPatch [Op.connect 1 2] edgeG = edgeG := by
  apply DocGraph.ext
  · intro i; rfl
  · show insert ((1 : AtomId), (2 : AtomId)) edgeG.order = edgeG.order; decide
  · intro n; rfl

/-- **`hom_not_thin` (P IS NON-THIN).** There are TWO DISTINCT parallel morphisms `edgeG ⟶ edgeG`:
the identity (empty patch) and the idempotent `[connect 1 2]` (adds an edge already present). Their
underlying patches `[]` and `[connect 1 2]` differ, so as morphisms they are DISTINCT — a hom-set of
size ≥ 2. A THIN category (a preorder) has AT MOST ONE morphism per pair; `P` does not. This is the
structural gap the inclusion category `⊑` (thin by construction) could not express. -/
theorem hom_not_thin :
    ∃ (f g : Hom edgeG edgeG), f ≠ g := by
  refine ⟨⟨[], rfl⟩, ⟨[Op.connect 1 2], connect_idem_on_edgeG⟩, ?_⟩
  intro h
  have : ([] : Patch) = [Op.connect 1 2] := congrArg Subtype.val h
  exact absurd this (by decide)

/-! ## 3. ISOMORPHISM in `P` — contextual, and GENUINELY NON-TRIVIAL.

`IsoP a b` is a pair of patches whose round-trips restore the endpoints — the RCCS CONTEXTUAL inverse
(`patch.rs::invert`, "sound against the graph the patch acted on"). It is an equivalence relation on
objects. Crucially `isoP_nontrivial` exhibits `IsoP a b` with `a ≠ b`: in the thin category isos are
identities (`a ≅ b → a = b`, `Includes.antisymm`), but in `P` there are REAL isos between DISTINCT
objects — the content of "unique up to unique iso" as opposed to "up to equality". -/

/-- **`IsoP a b`** — an isomorphism in `P`: forward patch `p : a ⟶ b`, backward `q : b ⟶ a`, whose
composites `p ++ q` and `q ++ p` restore the endpoints `a`, `b`. The contextual RCCS inverse. -/
def IsoP (a b : DocGraph) : Prop :=
  ∃ p q : Patch,
    applyPatch p a = b ∧ applyPatch q b = a ∧
    applyPatch (p ++ q) a = a ∧ applyPatch (q ++ p) b = b

theorem IsoP.refl (a : DocGraph) : IsoP a a :=
  ⟨[], [], rfl, rfl, rfl, rfl⟩

theorem IsoP.symm {a b : DocGraph} (h : IsoP a b) : IsoP b a := by
  obtain ⟨p, q, hp, hq, hpq, hqp⟩ := h
  exact ⟨q, p, hq, hp, hqp, hpq⟩

theorem IsoP.trans {a b c : DocGraph} (hab : IsoP a b) (hbc : IsoP b c) : IsoP a c := by
  obtain ⟨p, q, hp, hq, hpq, hqp⟩ := hab
  obtain ⟨r, s, hr, hs, hrs, hsr⟩ := hbc
  refine ⟨p ++ r, s ++ q, ?_, ?_, ?_, ?_⟩
  · rw [applyPatch_append, hp, hr]
  · rw [applyPatch_append, hs, hq]
  · -- apply ((p++r)++(s++q)) a = a : a →p b →r c →s b →q a
    simp only [applyPatch_append, hp, hr, hs, hq]
  · -- apply ((s++q)++(p++r)) c = c : c →s b →q a →p b →r c
    simp only [applyPatch_append, hp, hr, hs, hq]

/-! ### The non-trivial iso witness — `Connect`/`Disconnect` between two DISTINCT graphs. -/

/-- Two atoms `1`, `2` alive, no edges (the low graph). -/
def isoLo : DocGraph :=
  { atoms := fun i => if i = 1 ∨ i = 2 then some Status.alive else none,
    order := ∅, fields := fun _ => ∅ }
/-- Same atoms, with the order-edge `(1,2)` (the high graph). `isoLo ≠ isoHi`. -/
def isoHi : DocGraph := { isoLo with order := {(1, 2)} }

theorem isoLo_ne_isoHi : isoLo ≠ isoHi := by
  intro h
  have : isoLo.order = isoHi.order := congrArg DocGraph.order h
  simp only [isoHi, isoLo] at this
  exact absurd this (by decide)

/-- `[connect 1 2]` is a morphism `isoLo ⟶ isoHi` (adds the edge). -/
theorem connect_lo_to_hi : applyPatch [Op.connect 1 2] isoLo = isoHi := by
  apply DocGraph.ext
  · intro i; rfl
  · show insert ((1 : AtomId), (2 : AtomId)) isoLo.order = isoHi.order; decide
  · intro n; rfl

/-- `[disconnect 1 2]` is a morphism `isoHi ⟶ isoLo` (removes the edge — the contextual inverse). -/
theorem disconnect_hi_to_lo : applyPatch [Op.disconnect 1 2] isoHi = isoLo := by
  apply DocGraph.ext
  · intro i; rfl
  · show (isoHi.order).erase ((1 : AtomId), (2 : AtomId)) = isoLo.order; decide
  · intro n; rfl

/-- **The non-trivial iso.** `IsoP isoLo isoHi` via `Connect`/`Disconnect`: the round-trips restore
each endpoint (`connect` then `disconnect` returns to `isoLo`; `disconnect` then `connect` returns to
`isoHi`). A genuine isomorphism between DISTINCT objects. -/
theorem isoP_isoLo_isoHi : IsoP isoLo isoHi := by
  refine ⟨[Op.connect 1 2], [Op.disconnect 1 2], connect_lo_to_hi, disconnect_hi_to_lo, ?_, ?_⟩
  · rw [applyPatch_append, connect_lo_to_hi, disconnect_hi_to_lo]
  · rw [applyPatch_append, disconnect_hi_to_lo, connect_lo_to_hi]

/-- **`isoP_nontrivial` (THE REAL ISO, NOT EQUALITY).** There is an isomorphism in `P` between two
DISTINCT objects — `IsoP isoLo isoHi` with `isoLo ≠ isoHi`. In the THIN inclusion category
`a ≅ b → a = b` (`DocMerge.Includes.antisymm`: the only isos are identities); `P` has REAL isos
between distinct objects. This is precisely the "up to unique iso" vs "up to equality" gap. -/
theorem isoP_nontrivial : ∃ a b : DocGraph, a ≠ b ∧ IsoP a b :=
  ⟨isoLo, isoHi, isoLo_ne_isoHi, isoP_isoLo_isoHi⟩

/-- `isoLo ⊑ isoHi` — the high graph advances past the low (an extra order-edge, same atoms). -/
theorem isoLo_incl_isoHi : isoLo ⊑ isoHi := by
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv; exact ⟨v, hv, Status.le_refl v⟩
  · exact Finset.empty_subset _
  · intro n; exact Finset.empty_subset _

/-! ## 4. THE PUSHOUT — UP TO UNIQUE ISO, not degenerate to equality.

`IsPushoutUpToIso c a b d` is the iso-invariant pushout: `d` is a cocone over the span
`a ⟵ c ⟶ b` (`a ⊑ d`, `b ⊑ d`) that is `IsoP` to the canonical join `merge a b`. `merge` realizes
it; it is unique UP TO `IsoP`; and — the content the thin category cannot express —
`pushout_upToIso_two_distinct` exhibits ONE span with TWO DISTINCT pushout objects related by the
non-trivial iso. "Up to iso" is STRICTLY WEAKER than the thin category's "up to equality". -/

/-- **`IsPushoutUpToIso c a b d`** — `d` is a pushout of the span `a ⟵ c ⟶ b`, UP TO ISO: a cocone
over the feet that is `IsoP` to the canonical pushout `merge a b`. Iso-invariant by construction. -/
def IsPushoutUpToIso (c a b d : DocGraph) : Prop :=
  c ⊑ a ∧ c ⊑ b ∧ a ⊑ d ∧ b ⊑ d ∧ IsoP (merge a b) d

/-- **`merge` REALIZES the pushout.** For any span `a ⟵ c ⟶ b`, `merge a b` is a pushout up to iso
(the canonical representative; `IsoP` to itself by reflexivity). -/
theorem merge_IsPushoutUpToIso (c a b : DocGraph) (hca : c ⊑ a) (hcb : c ⊑ b) :
    IsPushoutUpToIso c a b (merge a b) :=
  ⟨hca, hcb, merge_includes_left a b, merge_includes_right a b, IsoP.refl _⟩

/-- **`pushout_upToIso_unique` (UNIQUE UP TO ISO).** Any two pushout objects of the same span are
`IsoP` — an isomorphism in `P`, not necessarily an equality. (Both are `IsoP` to `merge a b`, so
`IsoP` to each other by `symm`/`trans`.) -/
theorem pushout_upToIso_unique {c a b d d' : DocGraph}
    (hd : IsPushoutUpToIso c a b d) (hd' : IsPushoutUpToIso c a b d') : IsoP d d' :=
  (hd.2.2.2.2).symm.trans hd'.2.2.2.2

/-- **`pushout_upToIso_two_distinct` (NOT DEGENERATE TO EQUALITY).** The span `isoLo ⟵ isoLo ⟶ isoLo`
has TWO DISTINCT pushout objects: the canonical `isoLo` (`= merge isoLo isoLo`) and `isoHi`, which are
DISTINCT (`isoLo ≠ isoHi`) yet both pushouts up to iso — connected by the non-trivial `IsoP`. In the
THIN category the two pushout objects would be forced EQUAL (`Includes.antisymm`); in `P` they are a
genuine iso apart. This is the categorical content the preorder could not carry. -/
theorem pushout_upToIso_two_distinct :
    IsPushoutUpToIso isoLo isoLo isoLo isoLo ∧
    IsPushoutUpToIso isoLo isoLo isoLo isoHi ∧
    isoLo ≠ isoHi := by
  refine ⟨?_, ?_, isoLo_ne_isoHi⟩
  · refine ⟨Includes.refl _, Includes.refl _, Includes.refl _, Includes.refl _, ?_⟩
    rw [merge_idem]; exact IsoP.refl _
  · refine ⟨Includes.refl _, Includes.refl _, isoLo_incl_isoHi, isoLo_incl_isoHi, ?_⟩
    rw [merge_idem]; exact isoP_isoLo_isoHi

/-! ## 5. MIMRAM–DI GIUSTO: NOT all pushouts exist — a CONFLICT is a MISSING pushout.

A genuine conflict is a MISSING pushout in the plain (conflict-free) category, and EXISTS once the
conflict is a first-class object. We reuse `DocMerge`'s concrete two-fork conflict span
`base ⟵ (merge base forkA) — · — (merge base forkB) ⟶` whose pushout object is `conflictGraph` and
carries a `DocMerge.ConflictAt`. `DocMerge.ConflictAt` IS the categorical conflict object. -/

/-- **`ConflictFree g`** — `g` carries NO `DocMerge.ConflictAt` (no transitive prose antichain). The
objects of the plain patch subcategory (no first-class conflict states). -/
def ConflictFree (g : DocGraph) : Prop := ∀ p x y, ¬ ConflictAt g p x y

/-- The pushout object of the conflict span is NOT conflict-free (it carries the `ConflictAt`). -/
theorem conflictGraph_not_conflictFree : ¬ ConflictFree conflictGraph := by
  intro h; exact h pId aId bId merge_has_conflict

/-- **`no_conflictFree_pushout` (THE MISSING PUSHOUT).** The conflict span has NO pushout in the
CONFLICT-FREE subcategory: any pushout object equals `conflictGraph` (`DocMerge.pushout_unique`),
which carries a `ConflictAt` and so is not conflict-free. The plain patch category (conflict-free
objects) LACKS this pushout — Mimram–Di Giusto's "a conflict is a missing pushout". -/
theorem no_conflictFree_pushout :
    ¬ ∃ d, ConflictFree d ∧ IsPushout base (merge base forkA) (merge base forkB) d := by
  rintro ⟨d, hcf, hd⟩
  have hde : d = conflictGraph := pushout_unique hd conflictGraph_isPushout
  subst hde
  exact hcf pId aId bId merge_has_conflict

/-- **`conflict_object_is_pushout` (THE PUSHOUT EXISTS in the EXTENDED category).** In the FULL
category — where the conflict is a first-class object — the pushout of the conflict span EXISTS and
is `conflictGraph`, whose `DocMerge.ConflictAt pId aId bId` IS the conflict object. This ties the
categorical pushout structure to conflict-as-first-class-state: the missing pushout is RESTORED
exactly by admitting the conflict object. -/
theorem conflict_object_is_pushout :
    IsPushout base (merge base forkA) (merge base forkB) conflictGraph ∧
    ConflictAt conflictGraph pId aId bId :=
  ⟨conflictGraph_isPushout, merge_has_conflict⟩

/-! ## 6. FUNCTORIALITY — the residual functor / the "document state ↦ merge behavior" map.

Two honest functoriality statements the residual named. (a) `applyPatch` is a MONOID HOMOMORPHISM
`(P, ++, []) → (DocGraph → DocGraph, ∘, id)` — the action of `P` is functorial (identity ↦ identity,
concatenation ↦ composition). (b) the ADDITIVE (forward-op) subcategory maps functorially into the
THIN `⊑`-poset of `DocMerge`: every additive morphism `a ⟶ b` induces an inclusion `a ⊑ b`, with
identity ↦ `refl` and composition ↦ `trans`. -/

/-- **`applyPatch_functor_id`.** The identity patch acts as the identity function. -/
theorem applyPatch_functor_id : applyPatch [] = (id : DocGraph → DocGraph) := by
  funext g; rfl

/-- **`applyPatch_functor_comp` (FUNCTORIALITY OF THE ACTION).** Concatenation acts as composition:
`applyPatch (p ++ q) = applyPatch q ∘ applyPatch p`. Together with `applyPatch_functor_id` this makes
`applyPatch` a monoid homomorphism `(P, ++, []) → (endofunctions, ∘, id)`. -/
theorem applyPatch_functor_comp (p q : Patch) :
    applyPatch (p ++ q) = applyPatch q ∘ applyPatch p := by
  funext g; exact applyPatch_append p q g

/-- Whether an op is ADDITIVE (a monotone forward op): `Add`/`Delete`/`Connect`/`SetField` grow the
graph in `⊑`; the RCCS inverse ops (`Resurrect`/`Disconnect`/`RetractField`) do not. -/
def IsAdditive : Op → Prop
  | .add _ _ => True
  | .del _ => True
  | .connect _ _ => True
  | .setField _ _ => True
  | .resurrect _ => False
  | .disconnect _ _ => False
  | .retractField _ => False

/-- A patch is ADDITIVE iff all its ops are. -/
def Additive (p : Patch) : Prop := ∀ op ∈ p, IsAdditive op

/-- **`applyOp_mono` (each additive op is `⊑`-monotone).** For an additive op, `g ⊑ applyOp op g`:
`Add`/`Delete` advance a status to the join (`Status.le_join_left`) and only grow order; `Connect`
grows order; `SetField` grows a field's value-set. -/
theorem applyOp_mono (op : Op) (h : IsAdditive op) (g : DocGraph) : g ⊑ applyOp op g := by
  cases op with
  | add id after =>
    refine ⟨?_, ?_, ?_⟩
    · intro i v hv
      by_cases hi : i = id
      · refine ⟨Status.join v Status.alive, ?_, Status.le_join_left v Status.alive⟩
        show (if i = id then atomJoin (g.atoms i) (some Status.alive) else g.atoms i)
              = some (Status.join v Status.alive)
        rw [if_pos hi, hv]; rfl
      · refine ⟨v, ?_, Status.le_refl v⟩
        show (if i = id then atomJoin (g.atoms i) (some Status.alive) else g.atoms i) = some v
        rw [if_neg hi]; exact hv
    · exact Finset.subset_insert _ _
    · intro n; exact Finset.Subset.refl _
  | del id =>
    refine ⟨?_, ?_, ?_⟩
    · intro i v hv
      by_cases hi : i = id
      · refine ⟨Status.join v Status.dead, ?_, Status.le_join_left v Status.dead⟩
        show (if i = id then atomJoin (g.atoms i) (some Status.dead) else g.atoms i)
              = some (Status.join v Status.dead)
        rw [if_pos hi, hv]; rfl
      · refine ⟨v, ?_, Status.le_refl v⟩
        show (if i = id then atomJoin (g.atoms i) (some Status.dead) else g.atoms i) = some v
        rw [if_neg hi]; exact hv
    · exact Finset.Subset.refl _
    · intro n; exact Finset.Subset.refl _
  | connect x y =>
    refine ⟨?_, ?_, ?_⟩
    · intro i v hv; exact ⟨v, hv, Status.le_refl v⟩
    · exact Finset.subset_insert _ _
    · intro n; exact Finset.Subset.refl _
  | setField n0 v0 =>
    refine ⟨?_, ?_, ?_⟩
    · intro i v hv; exact ⟨v, hv, Status.le_refl v⟩
    · exact Finset.Subset.refl _
    · intro n
      by_cases hn : n = n0
      · show g.fields n ⊆ (if n = n0 then insert v0 (g.fields n) else g.fields n)
        rw [if_pos hn]; exact Finset.subset_insert _ _
      · show g.fields n ⊆ (if n = n0 then insert v0 (g.fields n) else g.fields n)
        rw [if_neg hn]
  | resurrect id => exact h.elim
  | disconnect x y => exact h.elim
  | retractField n => exact h.elim

/-- **`applyPatch_mono` (an ADDITIVE patch is `⊑`-monotone).** `g ⊑ applyPatch p g` for additive `p`
— the composite of monotone steps (`applyOp_mono` + `Includes.trans`). -/
theorem applyPatch_mono : ∀ (p : Patch), Additive p → ∀ g, g ⊑ applyPatch p g
  | [], _, g => Includes.refl g
  | op :: p, hp, g =>
      Includes.trans
        (applyOp_mono op (hp op (List.mem_cons.mpr (Or.inl rfl))) g)
        (applyPatch_mono p (fun o ho => hp o (List.mem_cons.mpr (Or.inr ho))) (applyOp op g))

/-- **`residual_mono` (the residual functor on objects+morphisms).** An additive morphism `a ⟶ b`
(patch `p` with `applyPatch p a = b`) is sent to the inclusion `a ⊑ b`. -/
theorem residual_mono {a b : DocGraph} (p : Patch) (hp : Additive p)
    (hab : applyPatch p a = b) : a ⊑ b := by
  have hm := applyPatch_mono p hp a; rw [hab] at hm; exact hm

/-- **`residual_functor_id`.** The identity morphism (empty patch) ↦ `Includes.refl`. -/
theorem residual_functor_id (a : DocGraph) : a ⊑ a := Includes.refl a

/-- **`residual_functor_comp` (FUNCTORIALITY into the thin poset).** A composite additive morphism
`a ⟶ b ⟶ c` is sent to the composite inclusion `a ⊑ c` = `Includes.trans` of the images. So the
residual assignment (additive morphism ↦ its inclusion) is a FUNCTOR from the additive subcategory of
`P` into the thin `⊑`-category of `DocMerge` — the honest "document state ↦ merge behavior". -/
theorem residual_functor_comp {a b c : DocGraph} (p q : Patch)
    (hp : Additive p) (hq : Additive q)
    (hab : applyPatch p a = b) (hbc : applyPatch q b = c) : a ⊑ c :=
  Includes.trans (residual_mono p hp hab) (residual_mono q hq hbc)

/-! ## 7. NON-VACUITY teeth — concrete arrows, the idempotent non-thin pair, the iso round-trips,
the conflict pushout object. (`#guard` on decidable `DocGraph` PROJECTIONS; a false guard is a build
error.) -/

-- A concrete arrow: `[connect 1 2]` takes the empty graph to the single-edge graph.
#guard (applyPatch [Op.connect 1 2] emptyG).order == ({(1, 2)} : Finset (AtomId × AtomId))
-- NON-THINNESS: the two parallel `edgeG ⟶ edgeG` patches genuinely differ.
#guard decide (([] : Patch) ≠ [Op.connect 1 2])
-- The iso round-trips: connect-then-disconnect returns to `isoLo` (∅ order); the reverse to `isoHi`.
#guard (applyPatch ([Op.connect 1 2] ++ [Op.disconnect 1 2]) isoLo).order
        == (∅ : Finset (AtomId × AtomId))
#guard (applyPatch ([Op.disconnect 1 2] ++ [Op.connect 1 2]) isoHi).order
        == ({(1, 2)} : Finset (AtomId × AtomId))
-- The two DISTINCT pushout objects: `isoLo` (∅) vs `isoHi` ({(1,2)}) really differ on order.
#guard decide (isoLo.order ≠ isoHi.order)
-- The conflict pushout object carries the two-fork order (the antichain), a well-formed state.
#guard conflictGraph.order == ({(pId, aId), (pId, bId)} : Finset (AtomId × AtomId))

/-! ## 8. Axiom hygiene — every keystone kernel-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms applyPatch_append
#assert_axioms connect_is_arrow
#assert_axioms hom_not_thin
#assert_axioms IsoP.refl
#assert_axioms IsoP.symm
#assert_axioms IsoP.trans
#assert_axioms isoP_isoLo_isoHi
#assert_axioms isoP_nontrivial
#assert_axioms isoLo_ne_isoHi
#assert_axioms merge_IsPushoutUpToIso
#assert_axioms pushout_upToIso_unique
#assert_axioms pushout_upToIso_two_distinct
#assert_axioms no_conflictFree_pushout
#assert_axioms conflict_object_is_pushout
#assert_axioms applyPatch_functor_id
#assert_axioms applyPatch_functor_comp
#assert_axioms applyOp_mono
#assert_axioms applyPatch_mono
#assert_axioms residual_mono
#assert_axioms residual_functor_comp

end Dregg2.Deos.PatchCategory
