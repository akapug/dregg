/-
# Dregg2.Exec.GatedForestCfg — first-class gated-forest carrier bundle.

Packages the `execFullForestG` carrier parameters as a `GatedForestCarriers` record, with
`starbridgeCarriers` the canonical production instance. Downstream modules `open StarbridgeGated`
instead of a pinned `Demo`/`Production` namespace.
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec

open FullForestAuth
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Spec (Guard)
open Dregg2.Exec.AuthModes (AuthMode AuthContext)

/-- **Carrier record** for the credential-gated call-forest executor. -/
structure GatedForestCarriers where
  digest : Type
  proof : Type
  request : Type
  stmt : Type
  wit : Type
  cellId : Type
  rights : Type
  ctx : Type
  gateway : Type
  bytes : Type
  tag : Type

/-! ## Starbridge — canonical production carriers + witness forests. -/

namespace StarbridgeGated

open Dregg2.Crypto.Reference

instance starbridgeVerifiable : Dregg2.Laws.Verifiable Nat Nat where
  Verify _ _ := true

def starbridgeCarriers : GatedForestCarriers where
  digest := Crypto.Reference.D
  proof := Crypto.Reference.P
  request := Bool
  stmt := Nat
  wit := Nat
  cellId := Label
  rights := Unit
  ctx := Nat
  gateway := Unit
  bytes := Nat
  tag := Nat

abbrev Dg := Crypto.Reference.D
abbrev Pf := Crypto.Reference.P
abbrev Rq := Bool
abbrev St := Nat
abbrev Wt := Nat
abbrev Cx := Nat
abbrev Gw := Unit
abbrev Bt := Nat
abbrev Tg := Nat
abbrev DNodeAuth := NodeAuth Dg Pf Rq St Wt Label Unit Cx Gw Bt Tg
abbrev DForest :=
  FullForestG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Unit) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)
abbrev DChild :=
  FullChildG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Unit) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- Fully-applied production forest step (`execFullForestG` at the starbridge carriers). -/
noncomputable def execForestG (s : RecChainedState) (f : DForest) : Option RecChainedState :=
  execFullForestG s f

def eraseForestG (f : DForest) : FullForestA :=
  eraseG f

theorem execForestG_erases (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    execFullForestA s (eraseForestG f) = some s' :=
  execFullForestG_erases s s' f h

def baseCapCtx : AuthContext Rq St Wt Label Unit Cx Gw :=
  { req := true, customStmt := 0, wit := fun _ => 0
  , registry := fun _ => none, caveatCtx := 150, discharges := fun _ => false
  , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }

def mkAuth (cred : Authorization Dg Pf) (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

def goodCred : Authorization Dg Pf := .signature 7 7
def forgedCred : Authorization Dg Pf := .signature 7 8

def trueCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (0 ≤ s.kernel.bal 0 0) }

def falseCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (10000 ≤ s.kernel.bal 0 0) }

def goodFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0
                , [ ({ holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                     , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 1 50, [] ⟩ } : DChild) ] ⟩ } : DChild) ] ⟩

def forgedCredForestG : DForest :=
  ⟨ mkAuth forgedCred [trueCaveat], .mintA 9 0 1 50, [] ⟩

def falseCaveatForestG : DForest :=
  ⟨ mkAuth goodCred [falseCaveat], .mintA 9 0 1 50, [] ⟩

def launderFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 0 50, [] ⟩ } : DChild) ] ⟩

#guard ((execFullForestG fmaDeleg goodFullForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 0) == 0
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 1) == 0
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)
#guard ((execFullForestG fmaDeleg forgedCredForestG).isSome) == false
#guard (credentialValidG forgedCredForestG.auth) == false
#guard (credentialValidG goodFullForestG.auth)
#guard ((execFullForestG fmaDeleg falseCaveatForestG).isSome) == false
#guard (caveatsDischarged falseCaveatForestG.auth fmaDeleg) == false
#guard (caveatsDischarged goodFullForestG.auth fmaDeleg)
#guard ((execFullForestG fmaDeleg launderFullForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 0) == -50
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 1) == 50
#guard ((execFullForestG fmaDeleg launderFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (55, 57)
#guard ((execFullForestA fmaDeleg (eraseG goodFullForestG)).isSome)
#guard (((execFullForestG fmaDeleg goodFullForestG).map (fun s => s.log.length)
        == (execFullForestA fmaDeleg (eraseG goodFullForestG)).map (fun s => s.log.length)))

end StarbridgeGated

end Dregg2.Exec