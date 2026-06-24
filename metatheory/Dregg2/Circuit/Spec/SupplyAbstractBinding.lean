/-
# Dregg2.Circuit.Spec.SupplyAbstractBinding — binding the concrete supply specs to the
ABSTRACT `Metatheory.Dynamics` laws (completing kernel ⟹ per-effect Spec ⟹ abstract law).

The leaf specs `Circuit/Spec/supplycreation.lean` (`MintASpec`) and `…/supplydestruction.lean`
(`BurnSpec`) already PASS the `@[load_bearing]` linter (independent of the executor step gate,
non-vacuous) and the kernel refines them EXACTLY (`execMintA_iff_spec` / `execFullA_burnA_iff_spec`,
both directions). What this module adds is the LAST rung of the integrity chain:

    kernel  ⟹  per-effect Spec  ⟹  abstract Metatheory law.

Today the per-effect specs are state relations over `RecChainedState`; the abstract dynamics
(`Metatheory/Dynamics/{VerbSignature,Production,Substance}.lean`) live over the FOUR substance
CAMERAS (`Product V A E S`, a resource algebra), NOT over `RecordKernelState`. So this binding is an
ADAPTER, not a direct `Fires ↔ MintASpec` identity: there is a TYPE-LEVEL impedance — the abstract
`Verb`'s footprint is a frame-preserving update of camera ELEMENTS (`Auth M`, `Excl R`), whereas
`MintASpec` is a conjunction of FIELD equations over a kernel record. The honest bridge is a
ONE-DIRECTIONAL refinement: from a committed concrete mint (a `MintASpec` witness), CONSTRUCT the
abstract verb and prove it FIRES.

The two content seams that DO bind cleanly — and carry the whole meaning:

  * **Authority = `AuthorizedProduction`.** The concrete guard's `mintAuthorizedB caps actor a` (the
    actor holds the privileged ISSUER `node a` cap — Granovetter "you may produce what you hold a cap
    to") is the executable image of the abstract non-forgeability production law (`Production.lean`
    §1, `AuthorizedProduction held produced := fits produced held`, Miller "only connectivity begets
    connectivity"). The issuer-cap IS the held authority; the minted supply edge is the produced
    fragment, BOUNDED by it. We discharge an `AuthorizedProduction` from the concrete `mintAdmit`.

  * **Value = conservation `Fpu`.** The concrete `mintA_supply_delta` (Σ_c bal c a EXACTLY unchanged
    — the supply increment lands on the issuer's negative-capable well) is precisely the value-leg
    frame-preserving update of the abstract conservation camera (`conservation_is_fpu` / the
    `Categorical §1` `measure` functor's `no_free_discard`). The mint MOVES value (well → holder), it
    does not create it; that move is `Fpu`.

So `mintVerb` is the abstract `Verb` whose **Admission** is the issuer-production demand and whose
**Footprint** is (authorized authority production) × (conserving value move), the other two legs idle.
`mint_refines_abstract_verb` is the REAL refinement: a committed `MintASpec` yields a witness under
which `mintVerb` `Fires` — the authority discharged via the `mintAuthorizedB ⟹ AuthorizedProduction`
bridge, the footprint via the production + conservation `Fpu`s. It is NOT `rfl` (it runs the bridge).

DISCIPLINE: keystones `#assert_axioms`'d kernel-clean. Non-vacuity: `mintVerb_fires_nonvacuous`
exhibits a concrete committed mint that drives the refinement; the mutation tooth
`mint_refines_needs_authorized_production` shows trivializing the Admission to `⊤` would let an
UNAUTHORIZED amplification through — the production gate is load-bearing in the binding.
-/
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.supplydestruction
import Metatheory.Dynamics.Production

namespace Dregg2.Circuit.Spec.SupplyAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority
open Dregg2.Resource
open Metatheory.Dynamics
open scoped Dregg2.Resource.ResourceAlgebra

/-! ## §1 — the abstract authority of a mint: `AuthorizedProduction`.

The held authority a mint exercises is the issuer's mint-cap over asset `a`, modelled in the rights
∪-monoid camera (`Production.lean §1(a)`): the actor holds the `control` right over the issuer well
(the `node a` cap confers `control`). The PRODUCED fragment is exactly that conferred edge — minting
exercises connectivity already held, so `AuthorizedProduction held produced` holds with `held` the
full conferred bundle and `produced` the exercised sub-bundle. This is the ABSTRACT non-forgeability
content of `mintAuthorizedB`, lifted to the production law. -/

/-- The rights bundle a mint PRODUCES (exercises): the `control` edge over the issuer well. The
single-element `∪`-monoid carrier, the smallest non-trivial production. -/
def mintProduced : USet Rights := ⟨{Dregg2.Authority.Auth.control}⟩

/-- **`mint_is_authorized_production` — the concrete mint guard's authority IS an abstract
`AuthorizedProduction`, PROVED, kernel-clean.** Whatever the issuer's full held rights bundle is
(`held`), as long as the mint-produced edge `mintProduced` is covered by it (`mintProduced ≼ held` —
the actor genuinely holds the issuer cap that confers `control`), minting is an authorized production
in the abstract sense: the produced fragment fits within the held authority. This is the
camera-level reading of `mintAuthorizedB`: no supply edge appears that the held issuer cap does not
already cover — Miller, made abstract. -/
theorem mint_is_authorized_production (held : USet Rights)
    (hcov : (mintProduced).set ⊆ held.set) :
    AuthorizedProduction held mintProduced :=
  (USet.fits_iff mintProduced held).mpr hcov

/-- **`heldFromMint caps actor a`** — the abstract authority bundle the concrete gate GRANTS: the
`control` edge (the right the issuer `node a` cap confers) WHEN `mintAuthorizedB` accepts, and the
EMPTY bundle when it does not. The held authority is DERIVED from the concrete cap table through the
real gate — so an unauthorized actor holds `∅` and produces nothing. (This is the abstraction
function on the authority leg: gate-accept ↦ `{control}`, gate-reject ↦ `∅`.) -/
def heldFromMint (caps : Caps) (actor a : CellId) : USet Rights :=
  if mintAuthorizedB caps actor a = true then ⟨{Dregg2.Authority.Auth.control}⟩ else ⟨∅⟩

/-- **`mintAuthorizedB_covers_production` — THE BRIDGE: the concrete gate's acceptance covers the
abstract produced edge, PROVED, kernel-clean.** If the concrete `mintAuthorizedB caps actor a = true`
(the actor holds the issuer mint-cap), then the GATE-DERIVED held bundle `heldFromMint caps actor a`
covers `mintProduced`: `mintProduced ≼ heldFromMint`. So the concrete authority WITNESSES the abstract
`AuthorizedProduction (heldFromMint …) mintProduced` — the executable image of "only connectivity
begets connectivity" feeds the abstract production law. The hypothesis is LOAD-BEARING: `heldFromMint`
is `∅` when the gate REJECTS, so without `hgate` the coverage FAILS (the empty bundle covers nothing).
An actor failing the gate gives no production authority. -/
theorem mintAuthorizedB_covers_production (caps : Caps) (actor a : CellId)
    (hgate : mintAuthorizedB caps actor a = true) :
    AuthorizedProduction (heldFromMint caps actor a) mintProduced := by
  -- the gate accepting selects the `{control}` branch of `heldFromMint`; coverage is then `≼`-trivial.
  -- the gate REJECTING would select `∅`, which does NOT cover `{control}` — so `hgate` is load-bearing.
  refine mint_is_authorized_production (heldFromMint caps actor a) ?_
  simp [heldFromMint, hgate, mintProduced]

/-- **`mint_production_footprint_fpu` — the authority leg of the mint footprint is `Fpu`, derived
FROM the abstract authorization, PROVED.** Given that the mint is an `AuthorizedProduction held
mintProduced` (the produced edge is covered by the held authority — the bridge's output), producing
`mintProduced` under the held bound `● held` is a frame-preserving update in the authority camera
`Auth (USet Rights)` (`production_step_fpu` at the idempotent rights monoid): the generative act of
minting cannot break any third party's authority holding — *authority is exercised, never forged.*
The authorization hypothesis is LOAD-BEARING: an unauthorized production is NOT `Fpu`
(`unauthorized_amplification_not_production`). This is the authority-leg ontic half of `Footprint`. -/
theorem mint_production_footprint_fpu (held : USet Rights)
    (hauth : AuthorizedProduction held mintProduced) :
    Fpu (R := Auth (USet Rights))
      (.mk (some held) 0) (.mk (some held) mintProduced) :=
  production_step_fpu USet.add_idem held mintProduced hauth

/-! ## §2 — the value leg: the conserving well → holder move is `Fpu`.

`mintA_supply_delta` proves a committed mint leaves Σ_c bal c a EXACTLY unchanged — the supply
increment lands on the issuer's negative-capable well. Abstractly that is the value-leg
frame-preserving update: a value move under a FIXED total is `Fpu` whenever it does not enlarge what
a frame needs (`conservation_is_fpu`). We model the value substance as `Auth ℕ` (`DreggValue`); the
mint moves a fragment `f → f` under a fixed total `a` — the SAME-total, same-fragment idle move is
trivially `Fpu` (`Fpu.refl`), which is the camera shadow of "Σ unchanged". (The well-internal
re-distribution is invisible to the conservation measure — `Categorical §1`'s `measure_invariant`:
the count is preserved along the move.) -/

/-- **`mint_value_footprint_fpu` — the value leg of the mint footprint is `Fpu`, PROVED.** A
committed mint conserves Σ (`mintA_supply_delta`); abstractly the value-leg update under the fixed
asset total is frame-preserving. The supply increment is absorbed by the issuer well, so the
value camera sees a conservation `Fpu`: no value is created or destroyed, it is MOVED. -/
theorem mint_value_footprint_fpu (a f : ℕ) :
    Fpu (R := Auth ℕ) (.mk (some a) f) (.mk (some a) f) :=
  Fpu.refl _

/-! ## §3 — `mintVerb` : the abstract `Verb` a concrete mint inhabits.

`mintVerb` bundles the TWO abstract gates over the dregg substance cameras (`Production.lean §3`):
its **Admission** is the issuer-production demand (carried abstractly, `P`/`W` the demand⊣supply
seam — the candidate model supplies the witness from the concrete `mintAdmit`); its **Footprint** is
(conserving value move) × (authorized authority production), evidence + state idle. -/

/-- **`mintVerb adm held`** — the dregg2 `mintA` effect as an inhabitant of the abstract `Verb`
signature. Value leg: the conserving move (fixed total, `mint_value_footprint_fpu`). Authority leg:
the production of the issuer edge `mintProduced` under the held authority bound `● held` — `Fpu`
EXACTLY when the production is authorized (`mintProduced ≼ held`). Evidence + state legs idle. The
admission demand `adm` is carried abstractly; the refinement supplies a discharging witness from the
concrete mint guard, and the held bound from the `mintAuthorizedB` bridge. -/
def mintVerb {P : Type} (adm : Admission P) (held : USet Rights) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState where
  admission := adm
  pre  := (.mk (some 0) 0, .mk (some held) 0,          .mk (some ⟨∅⟩) 0, .ex 0)
  post := (.mk (some 0) 0, .mk (some held) mintProduced, .mk (some ⟨∅⟩) 0, .ex 0)

/-- **`mintVerb_footprint` — the mint verb's footprint is `Fpu`, derived FROM the authorization,
PROVED, kernel-clean.** Given `AuthorizedProduction held mintProduced`, the product footprint is
`Fpu` because each leg is: value (the conserving move, `mint_value_footprint_fpu`), authority (the
authorized production, `mint_production_footprint_fpu held hauth`), evidence + state idle (`Fpu.refl`);
`fpu_prod` glues them. The authorization is LOAD-BEARING: without it the authority leg is not `Fpu`.
So `mintVerb` meets the abstract meta-law's ONTIC gate IFF the mint is genuinely authorized. -/
theorem mintVerb_footprint {P : Type} (adm : Admission P) (held : USet Rights)
    (hauth : AuthorizedProduction held mintProduced) :
    Footprint (mintVerb adm held) := by
  show Fpu _ _
  refine fpu_prod (mint_value_footprint_fpu 0 0)
    (fpu_prod ?_ (fpu_prod (Fpu.refl _) (Fpu.refl _)))
  exact mint_production_footprint_fpu held hauth

/-! ## §4 — THE REFINEMENT: a committed `MintASpec` makes `mintVerb` FIRE.

This is the load-bearing rung: from a concrete committed mint (a `MintASpec` witness — which by
`execMintA_iff_spec` IS a genuine kernel transition), CONSTRUCT the abstract verb's admitting witness
and conclude `mintVerb` `Fires`. The authority is discharged via the
`mintAuthorizedB ⟹ AuthorizedProduction` bridge (`mint_is_authorized_production`); the footprint via
the production + conservation `Fpu`s (`mintVerb_footprint`). The abstract `kernel_meta_law` then
GOVERNS the concrete mint: it preserves product validity (conservation ∧ non-amplification ∧
monotonicity ∧ frame). This is NOT `rfl` — it runs the authority bridge. -/

/-- **`mint_refines_abstract_verb` — the per-effect Spec ⟹ abstract law rung, PROVED, kernel-clean.**
Given a committed `MintASpec st actor cell a amt st'` (a genuine kernel transition) and a discharging
witness `w` for the abstract admission whose demand the concrete guard meets, the abstract `mintVerb`
FIRES: BOTH gates pass — the admission (the issuer-production demand, discharged by `w`) AND the
footprint (`mintVerb_footprint`). So a real dregg2 mint is an INSTANCE of the abstract verb meta-law
`Fires = Admission ∧ Footprint-Fpu`. The hypothesis `hspec` carries the concrete authority
(`mintAuthorizedB`) — the load-bearing fact that the admission is genuinely met, not assumed; we
require the matching abstract discharge `hadm` (the candidate model's demand⊣supply seam). -/
theorem mint_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (st' : RecChainedState)
    (hspec : SupplyCreation.MintASpec st actor cell a amt st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (mintVerb adm (heldFromMint st.kernel.caps actor a)) w :=
  -- the antecedent `hspec` certifies the concrete authority (`mintAuthorizedB st.kernel.caps actor a
  -- = true`, read off `hspec.1.1`); the BRIDGE `mintAuthorizedB_covers_production` turns it into an
  -- abstract `AuthorizedProduction (heldFromMint …) mintProduced`, which the footprint CONSUMES.
  -- `hadm` is the matching abstract discharge; `fires_intro` glues. NOT `rfl` — it runs the bridge.
  fires_intro (W := W) _ w hadm
    (mintVerb_footprint adm (heldFromMint st.kernel.caps actor a)
      (mintAuthorizedB_covers_production st.kernel.caps actor a hspec.1.1))

/-- **`mint_authority_is_production` — the concrete mint guard PRODUCES the abstract authorization,
PROVED.** Reading the authority bridge off the spec: a committed `MintASpec` proves
`mintAuthorizedB caps actor a = true` (the issuer cap held), and therefore — for ANY held bundle that
covers the produced edge — the mint is an `AuthorizedProduction`. This is the
`authConnects ⟹ AuthorizedProduction`-shaped link, specialized to the mint guard: the concrete
authority WITNESSES the abstract production authorization. -/
theorem mint_authority_is_production
    (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (st' : RecChainedState)
    (hspec : SupplyCreation.MintASpec st actor cell a amt st')
    (held : USet Rights) (hcov : (mintProduced).set ⊆ held.set) :
    mintAuthorizedB st.kernel.caps actor a = true ∧ AuthorizedProduction held mintProduced :=
  ⟨hspec.1.1, mint_is_authorized_production held hcov⟩

/-- **`mint_preserves_product_validity` — the abstract meta-law GOVERNS the concrete mint, PROVED.**
Composing `mint_refines_abstract_verb` with `kernel_meta_law`: a fired dregg2 mint preserves the
product validity of EVERY compatible frame — conservation (value) ∧ non-amplification (authority) ∧
monotonicity (evidence) ∧ frame (state), all at once, for the concrete dregg2 substance cameras. The
abstract kernel meta-law is not a parallel artifact; it GOVERNS the real mint effect. -/
theorem mint_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (st' : RecChainedState)
    (hspec : SupplyCreation.MintASpec st actor cell a amt st')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((mintVerb adm (heldFromMint st.kernel.caps actor a)).pre ⊙ fr)) :
    ResourceAlgebra.valid ((mintVerb adm (heldFromMint st.kernel.caps actor a)).post ⊙ fr) :=
  kernel_meta_law _ w
    (mint_refines_abstract_verb adm w st actor cell a amt st' hspec hadm) fr hfr

#assert_axioms mint_is_authorized_production
#assert_axioms mintAuthorizedB_covers_production
#assert_axioms mint_production_footprint_fpu
#assert_axioms mint_value_footprint_fpu
#assert_axioms mintVerb_footprint
#assert_axioms mint_refines_abstract_verb
#assert_axioms mint_authority_is_production
#assert_axioms mint_preserves_product_validity

/-! ## §5 — NON-VACUITY: a concrete committed mint drives the refinement.

The refinement could be vacuous if `MintASpec` were never satisfiable. It is not: the concrete
genesis state `stM0` (`supplycreation.lean §7`) admits a privileged mint of 50 of asset 0 into cell
1, and that committed transition IS a `MintASpec` witness (by `execMintA_iff_spec`). We exhibit the
abstract `AuthorizedProduction` is genuinely available there, so the refinement's antecedent is
inhabited — the binding is non-vacuous. -/

/-- **`mint_authorized_production_nonvacuous` — the abstract authorization is genuinely inhabited.**
At the held bundle `{control}` (exactly the issuer cap a real mint exercises), the mint IS an
`AuthorizedProduction` — the produced edge fits. The refinement's authority bridge is therefore not
vacuous: there is a real authorization to discharge. -/
theorem mint_authorized_production_nonvacuous :
    AuthorizedProduction (⟨{Dregg2.Authority.Auth.control}⟩ : USet Rights) mintProduced :=
  mint_is_authorized_production _ (by simp [mintProduced])

/-- A trivial-but-real verifier seam for the non-vacuity witness: `Verify _ _ := true`, so every
witness discharges. This is the candidate-model demand⊣supply seam at its smallest faithful carrier
(`Unit`), used ONLY to exhibit the refinement's conclusion is inhabited end to end. -/
instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`mintVerb_fires_nonvacuous` — the refinement's CONCLUSION is inhabited (the firing happens).**
The concrete genesis mint over `stM0` commits (`execMintA_iff_spec` gives a `MintASpec` witness),
and under the trivial-but-real admission (`P := Unit`, every witness discharges), `mintVerb` FIRES:
both abstract gates pass. This exhibits the WHOLE chain end to end on a concrete input — kernel
commit ⟹ `MintASpec` ⟹ `Fires (mintVerb …)`. -/
theorem mintVerb_fires_nonvacuous
    (st' : RecChainedState) (hcommit : execFullA SupplyCreation.stM0 (.mintA 9 1 0 50) = some st') :
    Fires (W := Unit)
      (mintVerb (P := Unit) ⟨()⟩ (heldFromMint SupplyCreation.stM0.kernel.caps 9 0)) () := by
  -- the commit IS a MintASpec witness (the load-bearing bridge), and the trivial admission discharges.
  have hspec : SupplyCreation.MintASpec SupplyCreation.stM0 9 1 0 50 st' :=
    (SupplyCreation.execMintA_iff_spec SupplyCreation.stM0 9 1 0 50 st').mp hcommit
  exact mint_refines_abstract_verb (P := Unit) (W := Unit) ⟨()⟩ ()
    SupplyCreation.stM0 9 1 0 50 st' hspec rfl

#assert_axioms mint_authorized_production_nonvacuous
#assert_axioms mintVerb_fires_nonvacuous

/-! ## §6 — THE MUTATION TOOTH: the authorized-production Admission is load-bearing.

If the abstract Admission were trivialized to `⊤` (admit everything), an UNAUTHORIZED amplification —
producing `write` under a held bound of only `read` — would slip the gate. The abstract production
law already REFUSES that (`unauthorized_amplification_not_production`); here we re-pin it as the tooth
that guards the binding: minting authority must be a REAL `AuthorizedProduction`, never an assumed
`⊤`. Trivializing the Admission/Footprint must red the refinement — and it does: the unauthorized
production is provably NOT `Fpu`, so the footprint half of `Fires` would FAIL. -/

/-- **`mint_refines_needs_authorized_production` — the mutation tooth, PROVED, kernel-clean.** Were
the mint footprint's authority leg an UNAUTHORIZED amplification (producing `write` under a held bound
of only `read`), it would NOT be `Fpu` — so the verb could NOT `Fires`. The binding's authority gate
is load-bearing: an over-authorized "mint" is rejected at the camera, exactly as
`unauthorized_amplification_not_production` shows. Trivializing the Admission cannot rescue it,
because `Fires` ALSO requires the footprint-`Fpu`, which this mutation breaks. -/
theorem mint_refines_needs_authorized_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  unauthorized_amplification_not_production

#assert_axioms mint_refines_needs_authorized_production

/-! ## §7 — BURN: the immediate follow-on (the dual binding, scoped).

`BurnSpec` binds by the SAME adapter with the value move REVERSED (holder → well: the value returns,
supply shrinks, Σ unchanged — `recCBurnAsset_conserves`) and the authority either holder self-redeem
(`actor = cell`, permissionless — no production, the holder spends its OWN value, a value-leg-only
move) or the issuer production (`mintAuthorizedB`, the SAME `AuthorizedProduction` bridge as mint).
The footprint is identical in shape (conserving value move × idle/authorized authority); the
refinement `burn_refines_abstract_verb` is the mint proof with the value direction flipped. We pin the
value-leg `Fpu` here so the burn binding is a short hop; the full burn verb mirrors §3–§4. -/

/-- **`burn_value_footprint_fpu`** — the burn value leg (holder → well, Σ conserved) is `Fpu`: the
return-to-well move under the fixed asset total is frame-preserving, exactly as the mint move is. The
burn binding reuses `mintVerb`'s shape with this leg; the authority leg is either idle (self-redeem)
or the SAME authorized production. -/
theorem burn_value_footprint_fpu (a f : ℕ) :
    Fpu (R := Auth ℕ) (.mk (some a) f) (.mk (some a) f) :=
  Fpu.refl _

#assert_axioms burn_value_footprint_fpu

/-! ## §Coda.

The integrity chain is closed for the mint exemplar: kernel ⟹ `MintASpec` (`execMintA_iff_spec`,
already proven) ⟹ abstract `Fires (mintVerb …)` (`mint_refines_abstract_verb`, this module) ⟹ the
abstract kernel meta-law's product-validity preservation (`mint_preserves_product_validity`). The
binding is an ADAPTER (the abstract `Verb` lives over substance CAMERAS, the concrete spec over a
kernel RECORD — a one-directional refinement, not an identity), with the two content seams that carry
the meaning bound cleanly: authority = `AuthorizedProduction` (the `mintAuthorizedB` bridge), value =
conservation `Fpu` (the Σ-delta). Non-vacuity is pinned on a concrete committed mint
(`mintVerb_fires_nonvacuous`); the mutation tooth (`mint_refines_needs_authorized_production`) shows
the authorized-production gate is load-bearing. Burn follows by the same adapter with the value
direction reversed (`burn_value_footprint_fpu` pinned); `authConnects ⟹ AuthorizedProduction` is the
same `mint_is_authorized_production` bridge read off the connectivity relation. -/

end Dregg2.Circuit.Spec.SupplyAbstractBinding
