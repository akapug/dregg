/-
# Dregg2.DSLEffect — the `dregg_effect <name> (args) : <Class>` effects eDSL.

Parses an effect declaration onto the proved `Spec.Conservation` conservation primitives
(`LinearityClass`, `requires_paired_sibling`, `is_disclosed_non_conservation`) and the
`CatalogEffects` discriminator (`Regime`, `Regime.ofClass`, `effectObligation`). Declaring
an effect's color generates (not hand-writes) its conservation obligation:

  * `Conservative`          ⇒ paired-sibling Σδ = 0 (`requires_paired_sibling = true`)
  * `Generative`/`Annihilative` ⇒ disclosed non-conservation (`is_disclosed_non_conservation = true`)
  * `Monotonic`/`Terminal`/`Neutral` ⇒ inert (neither paired nor disclosed)

The generated obligation is closed by the proved `CatalogEffects` per-class lemmas (or `rfl`).
The `(args)` are documentary (payload field names); an effect's linearity is a property of
its kind, not its payload values. Args may be omitted: `dregg_effect setField : Neutral`.
-/
import Dregg2.CatalogEffects
import Dregg2.Tactics      -- for the `#assert_axioms` / `#assert_namespace_axioms` honesty pins

namespace Dregg2.DSLEffect

open Dregg2.Spec Dregg2.Spec.LinearityClass
open Dregg2.CatalogEffects (Regime effectObligation)

/-! ## §1 — The syntax category for a `LinearityClass` color.

A fresh category `dregg_color` names the six `LinearityClass` colors as bare keywords, so an effect
declaration reads in surface English (`: Conservative`) rather than as a qualified term
(`: LinearityClass.Conservative`). Each color keyword elaborates to its exact `LinearityClass`
constructor — the parser-onto-proved-constructors discipline of DSL-A/B. -/

declare_syntax_cat dregg_color

syntax "Conservative" : dregg_color
syntax "Monotonic"    : dregg_color
syntax "Terminal"     : dregg_color
syntax "Generative"   : dregg_color
syntax "Annihilative" : dregg_color
syntax "Neutral"      : dregg_color

/-- Elaborate a `dregg_color` keyword to its exact `LinearityClass` constructor. -/
syntax (name := dreggColorElab) "dregg_color% " dregg_color : term
macro_rules
  | `(dregg_color% Conservative) => `(LinearityClass.Conservative)
  | `(dregg_color% Monotonic)    => `(LinearityClass.Monotonic)
  | `(dregg_color% Terminal)     => `(LinearityClass.Terminal)
  | `(dregg_color% Generative)   => `(LinearityClass.Generative)
  | `(dregg_color% Annihilative) => `(LinearityClass.Annihilative)
  | `(dregg_color% Neutral)      => `(LinearityClass.Neutral)

/-! ## §2 — The conservation obligation of a color.

`obligationProp c` is the proposition an effect of color `c` must satisfy, stated in the
`Spec.Conservation` vocabulary. The `def` is exhaustive — a new color cannot compile without
stating its obligation. -/

/-- The conservation obligation of a color, AS A PROPOSITION over the proved `Spec.Conservation`
classifiers. Exhaustive `match`, no default arm. -/
def obligationProp : LinearityClass → Prop
  | .Conservative => (LinearityClass.Conservative).requires_paired_sibling = true
  | .Generative   => (LinearityClass.Generative).is_disclosed_non_conservation = true
  | .Annihilative => (LinearityClass.Annihilative).is_disclosed_non_conservation = true
  | .Monotonic    => (LinearityClass.Monotonic).requires_paired_sibling = false ∧
                     (LinearityClass.Monotonic).is_disclosed_non_conservation = false
  | .Terminal     => (LinearityClass.Terminal).requires_paired_sibling = false ∧
                     (LinearityClass.Terminal).is_disclosed_non_conservation = false
  | .Neutral      => (LinearityClass.Neutral).requires_paired_sibling = false ∧
                     (LinearityClass.Neutral).is_disclosed_non_conservation = false

/-- Every color's obligation holds — discharged from `CatalogEffects` per-class theorems (or
equivalently by `rfl`, since the classifiers compute). This is the single proved fact the
`dregg_effect` command instantiates per declaration. -/
theorem obligation_holds : (c : LinearityClass) → obligationProp c
  | .Conservative => rfl
  | .Generative   => rfl
  | .Annihilative => rfl
  | .Monotonic    => ⟨rfl, rfl⟩
  | .Terminal     => ⟨rfl, rfl⟩
  | .Neutral      => ⟨rfl, rfl⟩

#assert_axioms obligation_holds

/-! ## §3 — The `dregg_effect` declaration command.

`dregg_effect <name> (a, …)? : <Color>` generates four declarations:
  * `def  <name>.color  : LinearityClass`
  * `def  <name>.regime : Regime`
  * `def  <name>.args   : List String`
  * `theorem <name>.obligation : obligationProp <name>.color := obligation_holds <name>.color`

A pure `macro` over the §1/§2 primitives. -/

/-- One payload-field name inside the `(args)` list — an identifier, recorded as its `String`. -/
syntax (name := dreggArgName) "dreggArgName% " ident : term
macro_rules
  | `(dreggArgName% $a:ident) => pure (Lean.Syntax.mkStrLit (toString a.getId))

/-- `dregg_effect <name> (a, …)? : <Color>` — declare an effect's color + inherited obligation. The
`(args)` are optional. Generates `<name>.color`, `<name>.regime`, `<name>.args`, and the proved
`<name>.obligation`. -/
syntax (name := dreggEffect)
  "dregg_effect " ident (" (" ident,* ")")? " : " dregg_color : command

macro_rules
  | `(dregg_effect $name:ident $[ ( $args,* ) ]? : $c:dregg_color) => do
      -- The dot-namespaced child names: `<name>.color`, `<name>.regime`, `<name>.args`, `<name>.obligation`.
      let colorName := name.getId ++ `color
      let regimeName := name.getId ++ `regime
      let argsName := name.getId ++ `args
      let oblName := name.getId ++ `obligation
      let colorId := Lean.mkIdent colorName
      let regimeId := Lean.mkIdent regimeName
      let argsId := Lean.mkIdent argsName
      let oblId := Lean.mkIdent oblName
      -- Parse the optional `(args)` into a `List String` syntax of the field names.
      let argStrs : Array (Lean.TSyntax `term) ←
        match args with
        | none => pure #[]
        | some as => as.getElems.mapM (fun a => `(dreggArgName% $a))
      `(/-- The `LinearityClass` coloring of this effect (generated by `dregg_effect`). -/
        def $colorId : LinearityClass := dregg_color% $c
        /-- The `CatalogEffects.Regime` (Paired/Disclosed/Inert) of this effect (generated). -/
        def $regimeId : Regime := Regime.ofClass (dregg_color% $c)
        /-- The documentary payload-field names of this effect (generated). -/
        def $argsId : List String := [ $argStrs,* ]
        /-- **The INHERITED conservation obligation of this effect — GENERATED, proved by the §2
        `obligation_holds` fact (NO hand-written proof).** Its statement is the
        `Spec.Conservation` obligation the color demands; its proof is the one already-proved fact. -/
        theorem $oblId : obligationProp $colorId := obligation_holds $colorId)

/-! ## §4 — Worked example: `transfer : Conservative`.

A transfer moves an `amount` of an `asset` between two cells. Its color is `Conservative` — its
per-domain deltas must sum to `0`. The declaration generates the `Paired` regime and the
paired-sibling obligation. -/

dregg_effect transfer (amount, asset, fromCell, toCell) : Conservative

/-- The declared `transfer` color IS exactly the `CatalogEffects` catalog coloring — proved by `rfl`. -/
theorem transfer_color_eq_catalog :
    transfer.color = Dregg2.CatalogInstances.effectLinearity .transfer := rfl

#assert_axioms transfer_color_eq_catalog

/-- The generated `transfer.regime` is the `Paired` regime (`Regime.ofClass .Conservative`). -/
theorem transfer_regime_eq : transfer.regime = Regime.Paired := rfl

/-- The generated obligation has the expected paired-sibling shape — and it is the `CatalogEffects`
class obligation `conservative_requires_paired` specialized to the catalog `transfer`. -/
example : transfer.color.requires_paired_sibling = true := transfer.obligation

/-- The documentary args are recorded verbatim. -/
example : transfer.args = ["amount", "asset", "fromCell", "toCell"] := rfl

#assert_axioms transfer_regime_eq

/-! ## §5 — Worked example: `mint : Generative`.

A mint creates an `amount` of an `asset` from nothing. Its color is `Generative` — it breaks
`Σδ = 0`, but the broken amount is disclosed (bound into the receipt). Generates the `Disclosed`
regime and the disclosure obligation. -/

dregg_effect mint (amount, asset) : Generative

/-- The declared `mint` color matches the catalog coloring of `bridgeMint` — proved by `rfl`.
(`mint` is the surface name for the `bridgeMint`/`createCell` generative family.) -/
theorem mint_color_eq_catalog :
    mint.color = Dregg2.CatalogInstances.effectLinearity .bridgeMint := rfl

#assert_axioms mint_color_eq_catalog

/-- The generated `mint.regime` is the `Disclosed` regime (`Regime.ofClass .Generative`). -/
theorem mint_regime_eq : mint.regime = Regime.Disclosed := rfl

/-- The generated obligation is the disclosure obligation — minting legitimately breaks conservation
but FORCES disclosure of the delta into the receipt. -/
example : mint.color.is_disclosed_non_conservation = true := mint.obligation

#assert_axioms mint_regime_eq

/-! ## §6 — Worked examples: `burn : Annihilative` and the three inert colors.

`burn` destroys a resource (`Annihilative`, dual of `Generative`): it breaks `Σδ = 0` and
discloses. The three inert colors (`Monotonic`/`Terminal`/`Neutral`) carry no conservation delta;
their obligation is "neither paired nor disclosed". -/

dregg_effect burn (amount, asset) : Annihilative
dregg_effect incrementNonce : Monotonic
dregg_effect cellDestroy : Terminal
dregg_effect setField (field, value) : Neutral

/-- `burn`'s color matches the catalog `burn` Annihilative variant — by `rfl`; obligation is disclosure. -/
theorem burn_color_eq_catalog :
    burn.color = Dregg2.CatalogInstances.effectLinearity .burn := rfl
example : burn.color.is_disclosed_non_conservation = true := burn.obligation
example : burn.regime = Regime.Disclosed := rfl

#assert_axioms burn_color_eq_catalog

/-- `incrementNonce` is `Monotonic` (inert): obligation is "neither paired nor disclosed". -/
theorem incrementNonce_color_eq_catalog :
    incrementNonce.color = Dregg2.CatalogInstances.effectLinearity .incrementNonce := rfl
example : incrementNonce.color.requires_paired_sibling = false ∧
          incrementNonce.color.is_disclosed_non_conservation = false := incrementNonce.obligation
example : incrementNonce.regime = Regime.Inert := rfl

#assert_axioms incrementNonce_color_eq_catalog

/-- `cellDestroy` is `Terminal` (one-way, no inverse) — inert. -/
theorem cellDestroy_color_eq_catalog :
    cellDestroy.color = Dregg2.CatalogInstances.effectLinearity .cellDestroy := rfl
example : cellDestroy.regime = Regime.Inert := rfl

#assert_axioms cellDestroy_color_eq_catalog

/-- `setField` is `Neutral` (pure book-keeping) — inert. It takes args but is not coloured by them,
confirming linearity is a property of the kind, not the payload values. -/
theorem setField_color_eq_catalog :
    setField.color = Dregg2.CatalogInstances.effectLinearity .setField := rfl
example : setField.color.requires_paired_sibling = false ∧
          setField.color.is_disclosed_non_conservation = false := setField.obligation
example : setField.regime = Regime.Inert := rfl

#assert_axioms setField_color_eq_catalog

/-! ## §7 — `effectObligation` coincidence.

Each declared effect's `.regime` coincides with `effectObligation` at its namesake catalog variant
— by `rfl`. -/

/-- The six declared regimes coincide with `CatalogEffects.effectObligation` at their catalog
variants — pinned by `rfl`. -/
theorem regimes_coincide_with_catalog :
    transfer.regime        = effectObligation .transfer ∧
    mint.regime            = effectObligation .bridgeMint ∧
    burn.regime            = effectObligation .burn ∧
    incrementNonce.regime  = effectObligation .incrementNonce ∧
    cellDestroy.regime     = effectObligation .cellDestroy ∧
    setField.regime        = effectObligation .setField :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms regimes_coincide_with_catalog

/-! ## §8 — build-enforced smoke-tests (the colors/regimes evaluate as declared). -/

#guard transfer.regime       = Regime.Paired
#guard mint.regime           = Regime.Disclosed
#guard burn.regime           = Regime.Disclosed
#guard incrementNonce.regime = Regime.Inert
#guard cellDestroy.regime    = Regime.Inert
#guard setField.regime       = Regime.Inert
#guard setField.args         = ["field", "value"]

/-! ## §9 — Axiom-hygiene tripwire.

Every theorem under `Dregg2.DSLEffect` — including the generated `<name>.obligation` theorems —
must rest only on the three kernel axioms. Any axiom outside that triple anywhere trips this. -/

#assert_namespace_axioms Dregg2.DSLEffect

end Dregg2.DSLEffect
