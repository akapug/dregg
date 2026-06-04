/-
# Dregg2.Intent.Match — the solver as a coend `∫^B`, and the bilateral lens fill.

Phase 2, layer 3 (`docs/rebuild/PHASE-2-INTENT-SPEC.md`; spine `INTENT-AS-CO-RECEIPT.md` §3,
`INTENT-REFS-optics.md`). Bilateral matching ("I want C, you offer C") is the easy case. A real
**exchange** routes demand to supply *through intermediate resources*: an intent `A ⊢ C` is filled by a
chain `A → B → C` assembled from available offers, existentially over the intermediate `B`. That
existential-over-the-middle is a **coend**:

```
  Match(A, C)  =  ∫^B  Offer(A → B) × Offer(B → C)          (solver = coend assembly)
```

This is the profunctor-optic / Tambara composition law, and the categorical content of an AMM router /
a multi-hop swap. We **reuse mathlib's coend** (`CategoryTheory.Limits.Types.coend`, brand-new in v4.30:
`coend F = Quot (coendRel F)` over the offer profunctor). For the offer profunctor, `Offer(A → B)` = the
free conversions `A ⟶ B` of the resource theory (a conversion IS an offer) — so the coend is the
density/co-Yoneda `∫^B (A ⟶ B) × (B ⟶ C)`, whose elements are the *routes* from `A` to `C`.

Per the spec: the FIRST app (the auction) models the bilateral fill as a simple **lens** (get/put) and
keeps the heavy coend for the multi-hop exchange — so the auction proof does NOT depend on the coend
machinery. We build the coend `Match` (non-vacuous; multi-hop typechecks) AND the lens fill; the auction
uses the lens. The coend's co-Yoneda *collapse* `Match A C ≅ (A ⟶ C)` is the standard theorem; its
mechanization (fighting the new `TypeCat` hom-coercion in the coend API) is deferred to when the
multi-hop router actually needs it — we keep the honest direction `Converts A C → Nonempty (Match A C)`.

Restricted to `[SmallCategory R]` (the auction's `DemoRes` is small) so the coend universes pin cleanly.
Pure; no `axiom`/`sorry`/`admit`/`native_decide`.
-/
import Mathlib.CategoryTheory.Limits.Types.End
import Mathlib.CategoryTheory.Functor.Currying
import Dregg2.Intent.Core

universe u

namespace Dregg2.Intent

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [SmallCategory R]

/-! ## 1. The offer profunctor `Offer(A → ·) × (· → C)`. -/

/-- **The offer pairing** `(X, Y) ↦ (A ⟶ Y) × (X ⟶ C)`: covariant in the covariant slot `Y` (an offer
into `Y` postcomposes), contravariant in `X` (an offer out of `X` precomposes). This is the bifunctor
whose coend over the diagonal is the solver. -/
def offerPairing (A C : R) : Rᵒᵖ × R ⥤ Type u where
  obj p := (A ⟶ p.2) × ((Opposite.unop p.1) ⟶ C)
  map {p q} f := ↾fun x => (x.1 ≫ f.2, f.1.unop ≫ x.2)

/-- The offer **profunctor** `Rᵒᵖ ⥤ R ⥤ Type`, curried for mathlib's coend. -/
def offerProf (A C : R) : Rᵒᵖ ⥤ R ⥤ Type u := Functor.curryObj (offerPairing A C)

/-! ## 2. `Match` = the coend (the multi-hop solver). -/

/-- **`Match A C = ∫^B (A ⟶ B) × (B ⟶ C)`** — the set of routes from `A` to `C` through some
intermediate resource `B`, as mathlib's coend `Quot (coendRel (offerProf A C))`. The coend quotients by
dinaturality (reparametrizing the intermediate `B`), so a route is identified with its composite. The
solver, first-class. -/
def Match (A C : R) : Type u := Types.coend.{u, u, u} (offerProf A C)

/-- **`oneHop k`** — a DIRECT conversion `k : A ⟶ C` as a one-hop route (intermediate `B := A`, with the
trivial first leg `𝟙 A`). Non-vacuity: every conversion is a match. -/
def oneHop {A C : R} (k : A ⟶ C) : Match A C := Quot.mk _ ⟨A, (𝟙 A, k)⟩

/-- **`twoHop B f g`** — a genuine MULTI-HOP route `A →[f] B →[g] C` through the intermediate `B`. This
typechecks as an element of `Match A C` — the `∫^B` is real (the auction's offer-generated resource
theory, Phase 4, populates it with non-identity offers; in the discrete demo `R`, routing forces the
hops through equal objects). -/
def twoHop {A C : R} (B : R) (f : A ⟶ B) (g : B ⟶ C) : Match A C := Quot.mk _ ⟨B, (f, g)⟩

/-- **`Converts A C → Nonempty (Match A C)`** — the match relation `⪰` (`Intent/Resource.lean`) lifts to
the solver: any convertibility witness is a (one-hop) route. The converse — collapsing a route back to a
single conversion (the co-Yoneda reduction `Match A C ≅ (A ⟶ C)`) — is the standard coend theorem,
deferred (the auction uses the lens fill §3, not the coend collapse). -/
theorem match_of_converts {A C : R} (h : Converts A C) : Nonempty (Match A C) :=
  h.elim fun k => ⟨oneHop k⟩

/-! ## 3. The bilateral lens fill (the auction's path — get/put optics).

`INTENT-REFS-optics.md`: an optic is a `get`/`put` pair. For a bilateral fill, the lens IS a direct
conversion: `get` extracts the offered `A`, `put` installs the produced `C`. No coend needed (the
intermediate is trivial). This is what the auction proof uses; `Match` (§2) is the multi-hop
generalization the lens embeds into (`toMatch`). -/

/-- **A bilateral lens fill** `A ⊸ C` — the get/put optic for a direct fill: it carries the conversion
`convert : A ⟶ C`. (`get` = the offered `A` consumed by `convert`; `put` = the produced `C`.) -/
structure LensFill (A C : R) where
  /-- The direct conversion filling the hole. -/
  convert : A ⟶ C

/-- A lens fill IS a convertibility witness (the thin match relation). -/
theorem LensFill.converts {A C : R} (l : LensFill A C) : Converts A C := ⟨l.convert⟩

/-- A bilateral lens fill embeds into the coend solver as a one-hop route — the lens is the trivial
case of the `∫^B`. -/
def LensFill.toMatch {A C : R} (l : LensFill A C) : Match A C := oneHop l.convert

/-! ## 4. Bridge to `Intent.fulfill` + non-vacuity on the demo resource theory. -/

/-- A fulfilled intent's receipt yields a bilateral lens fill `offered ⊸ outcome` (the conversion it
carries) — connecting the discharge keystone (`Intent/Core.lean`) to the solver layer. -/
def FillReceipt.lensFill {Stmt Wit : Type}
    {B : Dregg2.Authority.Blocklace.Lace} {reg : Dregg2.Authority.Predicate.Registry Stmt Wit}
    {stmtOf : Dregg2.Time.Frame.FrameStatement → Stmt} {i : Intent R B reg stmtOf}
    (r : FillReceipt i) : LensFill i.offered r.outcome :=
  { convert := r.conversion }

/-- **Non-vacuity: a concrete match exists** — the demo intent's fulfillment (`demoReceipt`, 1 art ⟶ 1
art) yields a lens fill, hence a one-hop route in `Match (res 0 1) (res 0 1)`. -/
def demoMatch : Match (res 0 1) (res 0 1) := demoReceipt.lensFill.toMatch

/-- **Non-vacuity: the multi-hop `∫^B` typechecks** — a two-hop route through the intermediate `res 0 1`
(in the discrete demo the hops are identities; Phase 4's offer-generated theory makes them real). -/
def demoMultiHop : Match (res 0 1) (res 0 1) :=
  twoHop (res 0 1) (𝟙 (res 0 1)) (𝟙 (res 0 1))

/-- The demo convertibility witness lifts to the solver. -/
theorem demo_match_nonempty : Nonempty (Match (res 0 1) (res 0 1)) :=
  match_of_converts (Converts.refl' _)

end Dregg2.Intent
