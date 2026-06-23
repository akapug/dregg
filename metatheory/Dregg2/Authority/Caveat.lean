/-
# Dregg2.Authority.Caveat — the keys-as-caps token layer (biscuit / macaroon / caveat / discharge).

Models dregg1's authority/credential framework (`Authorization::Token { encoded, key_ref, discharges }`
+ `TokenKeyRef`, `turn/src/action.rs:422`): the macaroon caveat chain, the biscuit delegation graph,
third-party caveats, and discharge.

Load-bearing content:
- a **token** = a `RootSeal` + an append-only attenuation chain of caveats (biscuit cross-vat /
  macaroon intra-vat), admitting a request iff all caveats are discharged (meet ⋀);
- **attenuation = appending a caveat = narrowing** — `attenuate_narrows` proves it can only shrink
  the admissible set ("a key may only narrow"; the Heyting residual `⇨`);
- the **biscuit/macaroon split = the vat boundary**: a biscuit is public-key verifiable off-island;
  a macaroon's HMAC root secret is held only by its scoping cell, so it is NOT third-party verifiable
  — a macaroon presented cross-domain is rejected;
- a **third-party caveat = the await engine's authority-face**: suspends until a named gateway's
  discharge resolves it (the discharge/`ConditionalTurn` isomorphism);
- **bridge to the verify/find seam**: a token's verification IS a `Laws.Discharged` witness.

Pure, computable, `#eval`-able.
-/
import Dregg2.Laws

namespace Dregg2.Authority

open Dregg2.Laws

/- The request binding-site `Ctx` — the `AuthRequest` facts a caveat is evaluated against (block
height, action, resource, sender, …). Abstract; instantiated by the real PI surface. `Gateway` =
the identity of a third-party caveat's resolving gateway. -/
variable {Ctx : Type}
variable {Gateway : Type}

/-! ## The reified caveat predicate AST (`CaveatPred`) — the D6 content-level vocabulary.

`Caveat.opaque` carries an *opaque* `Ctx → Bool`: you can RUN it, but you cannot reason about, print,
or structurally compare what it SAYS. `CaveatPred` is the introspectable twin — a small inductive AST
of *content-level* request-context atoms closed under the same `and`/`or`/`not`/`true`/`false`
connectives as `Exec.PredAlgebra.Pred`, so the caveat vocabulary is INSPECTABLE data, not a function.

**The fork question (honest).** `Exec.PredAlgebra.Pred` denotes over the `(old, new) : Value`
*transition* of a slot write; `CaveatPred` denotes over the *request context* `Ctx` (block height /
time / action / sender — the `AuthRequest` facts). The two share their CONNECTIVE shape
(`and`/`or`/`not`/`tt`/`ff`) but NOT their denotation domain, so a literal alias would be unsound. We
therefore MIRROR `Pred`'s connective layer here (zero re-fork of the connectives' meaning) while
keeping the atom layer request-context-typed. The atoms read `Ctx` through a `ReqView` seam (below),
so the AST itself stays pure data — `validAfter t` is a `Time`, not a captured closure.

**Honest framing (no overclaim).** This is an EXPRESSIVENESS / language gain — composable, printable,
structurally-comparable caveats and the content-level narrowing metatheory below — NOT a soundness
gain. The circuit still binds an aggregate `caveatBit` and trusts the executor's decision; reifying a
caveat does not force its policy in-circuit. -/

/-- **`ReqView Ctx`** — the seam by which a `CaveatPred` atom reads a request fact out of the abstract
context. Here: the request's `time` (the `validAfter` dimension). Instantiated by the real PI surface
(the `AuthRequest`); keeping it a class means the AST atoms stay pure DATA (`validAfter t` holds a
`Time`, never a closure) while remaining `Ctx`-abstract. -/
class ReqView (Ctx : Type) where
  /-- The request's logical time (block height / wall-clock tick), the field `validAfter` gates on. -/
  time : Ctx → Time

/-- **`CaveatPred`** — the reified, introspectable caveat AST. One real *content-level* atom
(`validAfter`, a temporal caveat: "this caveat admits only at request-time ≥ `t`" — the simplest
`DreggGrant` dimension) plus the Boolean connectives, mirroring `Exec.PredAlgebra.Pred`'s shape. A
`CaveatPred` is data you can PRINT, structurally compare, and refine — not an opaque `Ctx → Bool`. -/
inductive CaveatPred where
  /-- **`validAfter t`** — admits a request iff its time is `≥ t` (a "not-before" / temporal floor;
  the macaroon `time >` caveat / the `DreggGrant.validAfter` dimension), as inspectable data. -/
  | validAfter (t : Time)
  /-- Top — admits every request. -/
  | tt
  /-- Bottom — admits no request (fail-closed). -/
  | ff
  /-- Conjunction (meet). -/
  | and (l r : CaveatPred)
  /-- Disjunction (join). -/
  | or  (l r : CaveatPred)
  /-- Negation — at every level (mirroring `Pred.not`, not a single-level escape). -/
  | not (p : CaveatPred)
  deriving Repr, DecidableEq

/-- **`CaveatPred.eval`** — the denotation of the reified AST over a request context, reading facts
through `ReqView`. The structural fold mirrors `Pred.eval`: `validAfter t` admits iff `t ≤ time ctx`;
the connectives are `&&`/`||`/`!`/`true`/`false`. Decidable, computable, fail-closed (`ff` rejects). -/
def CaveatPred.eval [ReqView Ctx] : CaveatPred → Ctx → Bool
  | .validAfter t, ctx => decide (t ≤ ReqView.time ctx)
  | .tt,           _   => true
  | .ff,           _   => false
  | .and l r,      ctx => l.eval ctx && r.eval ctx
  | .or  l r,      ctx => l.eval ctx || r.eval ctx
  | .not p,        ctx => !(p.eval ctx)

/-- **A caveat** — the universal gate (`WitnessedCondition`), here in three engines: a **reified**
`CaveatPred` (introspectable content-level AST, D6), an **opaque** handwritten predicate over the
request context (the escape hatch for caveats not yet in the AST vocabulary — `local` renamed: it IS
opaque), or a **third-party** caveat naming a `gateway` that must *discharge* it (the await
authority-face). -/
inductive Caveat (Ctx Gateway : Type) where
  | pred       (p : CaveatPred)
  | opaque     (check : Ctx → Bool)
  | thirdParty (gateway : Gateway)

/-- The discharges presented alongside a token (dregg1 `Authorization::Token.discharges`): which
gateways have produced a resolution. -/
abbrev Discharges (Gateway : Type) := Gateway → Bool

/-- A caveat is satisfied at a request iff its reified `CaveatPred` admits, its opaque check holds, or
its gateway has discharged. The reified arm folds through `CaveatPred.eval` (so a `pred`-caveat is an
inspectable policy), the opaque arm just RUNS its closure. -/
def Caveat.ok [ReqView Ctx] (c : Caveat Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  match c with
  | .pred p       => p.eval ctx
  | .opaque check => check ctx
  | .thirdParty g => d g

/-- The two token carriers (dregg1 `TokenKeyRef`). -/
inductive TokenKind where
  /-- **biscuit** (`eb2_…`): cross-vat — Ed25519 public-key, offline-verifiable by *anyone*; the
  biscuit delegation graph ≡ the distributed CDT. -/
  | biscuit
  /-- **macaroon** (`em2_…`): intra-vat — a cell-scoped HMAC; the root secret is held only by the
  scoping cell, so it is NOT third-party-verifiable (`discoveries §6.3`). -/
  | macaroon
  deriving DecidableEq, Repr

/-- **A token** — a kind (biscuit/macaroon) + an **append-only attenuation chain of caveats**. The
chain *is* the path of monotone-narrowing `(parent → child)` edges from a `RootSeal` (the CDT
rendering); authority = the meet of all caveats. -/
structure Token (Ctx Gateway : Type) where
  kind    : TokenKind
  caveats : List (Caveat Ctx Gateway)

/-- **A token admits a request iff ALL its caveats are satisfied** (the conjunction / meet ⋀) — the
fail-closed authority decision. -/
def Token.admits [ReqView Ctx] (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  tok.caveats.all (fun c => c.ok ctx d)

/-- **Attenuation = appending a caveat** — the *one rule the system rests on* (`dregg2 §1.1`):
narrowing only. A child token = `attenuate parent cav`. -/
def Token.attenuate (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway) : Token Ctx Gateway :=
  { tok with caveats := tok.caveats ++ [c] }

/-! ## The keystone — attenuation can only NARROW (the LossyMorphism, realized). -/

/-- **`attenuate_narrows`** — anything an attenuated token admits, the parent already admitted:
adding a caveat never grows authority. The concrete realization of "a key may only narrow"
(the Heyting residual `⇨`) on the actual biscuit/macaroon chain. -/
theorem attenuate_narrows [ReqView Ctx] (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate c).admits ctx d = true → tok.admits ctx d = true := by
  simp only [Token.admits, Token.attenuate, List.all_append, Bool.and_eq_true]
  intro h; exact h.1

/-- **`attenuate_subset`** — set form: a more-attenuated token's admissible-request set is a
subset of the parent's. Authority strictly shrinks down a delegation chain. -/
theorem attenuate_subset [ReqView Ctx] (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (d : Discharges Gateway) :
    {ctx | (tok.attenuate c).admits ctx d = true} ⊆ {ctx | tok.admits ctx d = true} :=
  fun ctx h => attenuate_narrows tok c ctx d h

/-- Attenuating by an always-true caveat leaves authority unchanged (the trivial
attenuation = identity edge). Sanity companion to `attenuate_narrows`. -/
theorem attenuate_trivial [ReqView Ctx] (tok : Token Ctx Gateway) (ctx : Ctx)
    (d : Discharges Gateway) :
    (tok.attenuate (.opaque (fun _ => true))).admits ctx d = tok.admits ctx d := by
  simp [Token.admits, Token.attenuate, List.all_append, Caveat.ok]

/-! ## The biscuit / macaroon split IS the vat boundary. -/

/-- Only a biscuit verifies off-island (public-key); a macaroon's HMAC root secret is held
only by its scoping cell, so a non-holder cannot verify it (HMAC ≠ third-party-verifiable). -/
def Token.crossVatVerifiable (tok : Token Ctx Gateway) : Bool :=
  match tok.kind with | .biscuit => true | .macaroon => false

/-- **A macaroon is never cross-vat verifiable.** Presenting it to a non-holding verifier
fails closed: off-island keys-as-caps is the biscuit's job, not the macaroon's. -/
theorem macaroon_not_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .macaroon) :
    tok.crossVatVerifiable = false := by
  unfold Token.crossVatVerifiable; rw [h]

/-- **A biscuit is cross-vat verifiable** (the `Obs` badge that leaves the vat). -/
theorem biscuit_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .biscuit) :
    tok.crossVatVerifiable = true := by
  unfold Token.crossVatVerifiable; rw [h]

/-! ## Bridge to the verify/find seam: a verifying token IS a `Laws.Discharged` witness. -/

/-- A token (with its discharges) instantiates the verify/find seam (`Laws.Verifiable`): the
predicate is the request context, the witness is the `(token, discharges)` pair, and `Verify` is
`Token.admits`. The token layer is a `Verify` — biscuit and STARK are both witnesses differing
only in cost. -/
instance tokenVerifiable [ReqView Ctx] : Verifiable Ctx (Token Ctx Gateway × Discharges Gateway) where
  Verify ctx w := w.1.admits ctx w.2

/-- **`token_discharges`** — a token that admits the request is a discharged verify/find-seam
witness. The cap's authorization across the boundary is a `Verify`, feeding the cross-vat case
of the vat-boundary law. -/
theorem token_discharges [ReqView Ctx] (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway)
    (h : tok.admits ctx d = true) :
    Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway) ctx (tok, d) := h

/-! ## It runs (`#eval`) — a macaroon attenuated down a chain. -/

/-- A toy request context: the current block height. -/
abbrev Height := Nat

/-- The toy `ReqView`: a block height IS the request's logical time. (A `CaveatPred.validAfter t`
over a `Height` request gates on "height ≥ t".) -/
instance : ReqView Height where time h := (h : Int)

/-- A root biscuit with no caveats (full authority over its target). -/
def rootBiscuit : Token Height Unit := { kind := .biscuit, caveats := [] }

/-- Attenuate it with "height ≥ 100" then "height ≤ 200" — a validity window. The lower bound is the
REIFIED `validAfter 100` caveat (`CaveatPred`, inspectable); the upper bound stays an `opaque` check
(no `validBefore` atom in the toy AST yet — the escape hatch carries it, nothing regresses). -/
def windowed : Token Height Unit :=
  (rootBiscuit.attenuate (.pred (.validAfter 100))).attenuate (.opaque (fun h => decide (h ≤ 200)))

/-- No discharges needed (no third-party caveats). -/
def noDischarges : Discharges Unit := fun _ => false

#guard rootBiscuit.admits 150 noDischarges           -- root admits everything
#guard windowed.admits 150 noDischarges              -- 150 ∈ [100,200]
#guard windowed.admits 50  noDischarges == false     -- 50 < 100 — a caveat narrowed it out
#guard windowed.admits 250 noDischarges == false     -- 250 > 200
#guard windowed.crossVatVerifiable                   -- a biscuit travels off-island
#guard rootBiscuit.crossVatVerifiable

/-- A macaroon version of the same window — cannot be verified off-island. -/
def macWindowed : Token Height Unit := { windowed with kind := .macaroon }
#guard macWindowed.crossVatVerifiable == false   -- HMAC ≠ third-party-verifiable

/-- A third-party caveat: this turn cannot become admissible until gateway `()` discharges it
(the await authority-face). -/
def needsGateway : Token Height Unit := windowed.attenuate (.thirdParty ())
#guard needsGateway.admits 150 (fun _ => false) == false  -- gateway has not discharged
#guard needsGateway.admits 150 (fun _ => true)            -- gateway discharged ⇒ suspended turn resolves

end Dregg2.Authority
