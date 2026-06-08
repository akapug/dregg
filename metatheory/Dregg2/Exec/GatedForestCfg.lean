/-
# Dregg2.Exec.GatedForestCfg — first-class gated-forest carrier bundle.

Packages the `execFullForestG` carrier parameters as a `GatedForestCarriers` record, with
`starbridgeCarriers` the canonical production instance. Downstream modules `open StarbridgeGated`
instead of a pinned `Demo`/`Production` namespace.

**Production routing for `.coordinated` caveats:** intra-cell `execFullForestG` fail-closes
(see `FullForestAuth.GatedCaveat.holds`); the positive bilateral path is
`CoordinatedForestGLift.execCoordinatedForestG` over a `BilateralForestPairG` of two
`RecChainedState` snapshots (honest — no cross-cell reads on one cell).
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec

open FullForestAuth
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Spec (Guard)
open Dregg2.Exec.AuthModes (AuthMode AuthContext unchecked_unconstrained_admits)
open Dregg2.Crypto.Reference
open Dregg2.Exec (ExecAuth confRights attenuate)

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
  rights := ExecAuth
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
/-- The production rights lattice (the REAL `Finset Auth ⊆` order — `granted ≤ held` is now
non-vacuous, unlike the previous `Unit` collapse). -/
abbrev Rt := ExecAuth
abbrev DNodeAuth := NodeAuth Dg Pf Rq St Wt Label Rt Cx Gw Bt Tg
abbrev DForest :=
  FullForestG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)
abbrev DChild :=
  FullChildG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- Fully-applied production forest step (`execFullForestG` at the starbridge carriers). -/
noncomputable def execForestG (s : RecChainedState) (f : DForest) : Option RecChainedState :=
  execFullForestG s f

def eraseForestG (f : DForest) : FullForestA :=
  eraseG f

theorem execForestG_erases (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    execFullForestA s (eraseForestG f) = some s' :=
  execFullForestG_erases s s' f h

/-- Childless gated forest = single gated node step. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a <;> rfl

def baseCapCtx : AuthContext Rq St Wt Label Rt Cx Gw :=
  { req := true, customStmt := 0, wit := fun _ => 0
  , registry := fun _ => none, caveatCtx := 150, discharges := fun _ => false
  , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }

def mkAuth (cred : Authorization Dg Pf) (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-! ### A1 — the REAL-RIGHTS cap-authority leg (the WHAT, now load-bearing).

`mkAuth` pins `capMode := .unchecked (Guard.all [])`, which `authModeAdmits` admits for ALL inputs —
so the proved `granted ≤ held` attenuation theory was proved-but-never-exercised over the wire. Here
we route the delegation edge's `keep`/`parentCap` into a `.capTpDelivered` cap mode whose
`granted := keep.toFinset` and `held := confRights parentCap` over the REAL `ExecAuth = Finset Auth`
lattice. `authModeAdmits (.capTpDelivered ⟨_,_,held,granted⟩ _) = decide (granted.rights ≤ held.rights)
&& facetOk && freshOk`, so a delegation edge that AMPLIFIES (`keep ⊄ parentCap.rights`) makes the WHAT
leg FALSE ⇒ the gate fail-closes ⇒ whole-turn rollback. This makes the attenuation theory load-bearing
at the wire. -/

/-- The target label of a positional `Cap` (`null` targets the agent cell `0` by convention; only
the rights matter for the attenuation check). -/
def capTargetOf : Cap → Label
  | .null         => 0
  | .endpoint t _ => t
  | .node t       => t

/-- Build a `.capTpDelivered` cap mode that gates the delegated `keep` rights against the parent
cap's conferred rights over the real `ExecAuth` lattice. `held := confRights parentCap`,
`granted := keep.toFinset`; admits iff `keep.toFinset ≤ confRights parentCap` (the non-amplifying
discipline `is_attenuation(held, granted)`), with facet/freshness already `true` in `baseCapCtx`. -/
def capModeOfEdge (holder : Label) (keep : List Auth) (parentCap : Cap) :
    AuthMode Rq St Wt Label Rt Cx Gw :=
  .capTpDelivered
    { introducer := holder, recipient := holder
    , held := { target := capTargetOf parentCap, rights := confRights parentCap }
    , granted := { target := capTargetOf parentCap, rights := keep.toFinset } }
    True

/-- A node-auth whose WHAT leg gates on the delegation edge's real-rights attenuation. The WHO
(credential) and caveats are the same as `mkAuth`; only `capMode` is the load-bearing
`capModeOfEdge holder keep parentCap`. -/
def mkAuthCap (cred : Authorization Dg Pf) (caveats : List GatedCaveat)
    (holder : Label) (keep : List Auth) (parentCap : Cap) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := capModeOfEdge holder keep parentCap, capCtx := baseCapCtx
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

/-- Gated forest erasing to the canonical `transferCF` (actor 0, cell 0→1, asset 0). -/
def transferForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0, [] ⟩

/-- Single-node gated forest for production `◇` witnesses: one `emitEvent`, balance-neutral. -/
def logBumpForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

theorem transferForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG transferForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, transferForestG, ledgerDeltaAsset,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem logBumpForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG logBumpForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, logBumpForestG, ledgerDeltaAsset,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]

/-- The log-bump forest shares the good-credential root auth with `goodFullForestG`. -/
theorem logBumpForestG_auth_eq : logBumpForestG.auth = goodFullForestG.auth := rfl

theorem logBumpForestG_credential_valid : credentialValidG logBumpForestG.auth = true := by
  unfold logBumpForestG credentialValidG mkAuth goodCred
  decide

theorem logBumpForestG_cap_authority : capAuthorityG logBumpForestG.auth = true := by
  unfold logBumpForestG capAuthorityG mkAuth
  exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)

theorem logBumpForestG_caveats_fma0 : caveatsDischarged logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG caveatsDischarged mkAuth trueCaveat baseCapCtx chainGateG fma0
  simp only [List.all_cons, List.all_nil, Bool.and_true, GatedCaveat.holds, decide_eq_true_eq]
  norm_num

theorem logBumpForestG_revocation_fma0 : revocationGate logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG revocationGate mkAuth fma0
  simp

/-- Gate legs for the log-bump witness forest at `fma0`. -/
theorem logBumpForestG_gateOK : gateOK logBumpForestG.auth fma0 = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, logBumpForestG_credential_valid, logBumpForestG_cap_authority,
             logBumpForestG_caveats_fma0, logBumpForestG_revocation_fma0]
  trivial

theorem transferForestG_auth_eq : transferForestG.auth = logBumpForestG.auth := rfl

theorem transferForestG_gateOK : gateOK transferForestG.auth fma0 = true := by
  rw [transferForestG_auth_eq]
  exact logBumpForestG_gateOK

theorem transferForestG_erase_eq :
    eraseForestG transferForestG = ⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩ := rfl

theorem transferForestG_kernel_commits :
    (execFullForestA fma0 (eraseForestG transferForestG)).isSome := by decide

theorem transferForestG_commits : (execFullForestG fma0 transferForestG).isSome := by
  rcases Option.isSome_iff_exists.mp transferForestG_kernel_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, transferForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0)).mpr
    ⟨transferForestG_gateOK, hs'⟩
  simpa [hga]

/-- The erased log-bump action commits at `fma0` (authority-free emit on a live cell). -/
theorem logBump_erase_commits : (execFullForestA fma0 (eraseG logBumpForestG)).isSome := by decide

/-- The production log-bump forest COMMITS at `fma0` (gate + credential + caveat all pass). -/
theorem logBumpForestG_commits : (execFullForestG fma0 logBumpForestG).isSome := by
  rcases Option.isSome_iff_exists.mp logBump_erase_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, logBumpForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.emitEventA 0 0 0 0)).mpr
    ⟨logBumpForestG_gateOK, hs'⟩
  simpa [hga]

/-- The committed post-state lands exactly one receipt. -/
theorem logBumpForestG_log_one {s' : RecChainedState}
    (h : execFullForestG fma0 logBumpForestG = some s') : s'.log.length = 1 := by
  have herase := execFullForestG_erases fma0 s' logBumpForestG h
  have hlen : (execFullForestA fma0 (eraseG logBumpForestG)).map (fun s => s.log.length) = some 1 := by
    decide
  rw [herase] at hlen
  simpa using hlen

#guard ((execFullForestG fma0 logBumpForestG).isSome)
#guard ((execFullForestG fma0 logBumpForestG).map (fun s => s.log.length) == some 1)

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
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s' => decide (fmaDeleg.log.length < s'.log.length)) == some true)

/-! ### A1 — the WHAT leg (`capAuthorityG`) now has REAL TEETH at the wire.

The two forests below share EVERYTHING — the same genuine credential, the same caveat, the same
`emitEvent` action — differing ONLY in the delegated edge's `keep`/`parentCap`. The non-amplifying
one (`keep = [read]` against a parent cap `.endpoint 0 [read,write]`) COMMITS; the amplifying one
(`keep = [read,write]` against a parent cap `.endpoint 0 [read]`) is REJECTED by `capAuthorityG`
(`granted ⊄ held` over `ExecAuth`) ⇒ the whole forest rolls back. The previous `.unchecked` cap mode
admitted BOTH. This is the same-wire contrast proving the proved `granted ≤ held` attenuation is now
load-bearing — no longer admit-by-construction. -/

/-- A non-amplifying delegated node: `keep = [read]` ⊆ parent rights `[read, write]`. Its WHAT leg
ADMITS (`[read].toFinset ≤ {read, write}`). Balance-neutral `emitEvent`. -/
def capOkForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read] (.endpoint 0 [Auth.read, Auth.write])
  , .emitEventA 0 0 0 0, [] ⟩

/-- An AMPLIFYING delegated node: `keep = [read, write]` ⊄ parent rights `[read]`. Its WHAT leg
REJECTS (`{read, write} ⊄ {read}`). The ONLY difference from `capOkForestG` is the cap data. -/
def capAmplifyForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write] (.endpoint 0 [Auth.read])
  , .emitEventA 0 0 0 0, [] ⟩

-- The WHAT leg ADMITS the non-amplifying edge but REJECTS the amplifying one:
#guard (capAuthorityG capOkForestG.auth)                  --  true  (keep ⊆ parent)
#guard (capAuthorityG capAmplifyForestG.auth) == false    --  false (keep ⊄ parent: AMPLIFY)
-- ...and the gate (hence the whole forest) follows the WHAT leg — the amplifying turn ROLLS BACK:
#guard ((execFullForestG fma0 capOkForestG).isSome)               --  true  (commits)
#guard ((execFullForestG fma0 capAmplifyForestG).isSome) == false --  false (gate rejects ⇒ rollback)
-- The two differ ONLY in cap data (same credential ⇒ same WHO leg passes for both):
#guard (credentialValidG capOkForestG.auth)
#guard (credentialValidG capAmplifyForestG.auth)
-- An EXACT-rights (equal, not strict subset) edge also admits (reflexivity of attenuation):
#guard (capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
          (.endpoint 0 [Auth.read, Auth.write])))  --  true

theorem capOkForestG_what_admits : capAuthorityG capOkForestG.auth = true := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read]
        (.endpoint 0 [Auth.read, Auth.write])) = true
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

theorem capAmplifyForestG_what_rejects : capAuthorityG capAmplifyForestG.auth = false := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
        (.endpoint 0 [Auth.read])) = false
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

/-- The amplifying forest is REJECTED by the full gate (the WHAT leg fail-closes the conjunction). -/
theorem capAmplifyForestG_gate_rejects : gateOK capAmplifyForestG.auth fma0 = false := by
  unfold gateOK
  rw [capAmplifyForestG_what_rejects]
  simp

/-- Hence the amplifying forest does NOT commit (`execFullForestG = none`). -/
theorem capAmplifyForestG_rolls_back : execFullForestG fma0 capAmplifyForestG = none := by
  unfold capAmplifyForestG
  show (match execFullAGated fma0 _ (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG _ s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  have : gateOK capAmplifyForestG.auth fma0 = false := capAmplifyForestG_gate_rejects
  unfold capAmplifyForestG at this
  simp only [this]
  rfl

#assert_axioms capAmplifyForestG_what_rejects
#assert_axioms capOkForestG_what_admits
#assert_axioms capAmplifyForestG_gate_rejects
#assert_axioms capAmplifyForestG_rolls_back

/-! ### A2 — the AGENT-FACING `Authorization::Token` path (the biscuit credential the Rust
SubAgent / node-MCP surface constructs), now gating the EXECUTOR on the SAME live `execFullForestG`
path — both the WHO (biscuit signature) and the WHAT (the token's attenuation caveats) leg.

The Rust `sdk::SubAgent::execute` / `node::mcp::dispatch_tool` surfaces mint a public-key biscuit
and present it as `Authorization::Token`; the EXECUTOR (`verify_token_for_scope` /
`verify_token_authorization`), not an out-of-band `cap.verify()`, admits or rejects the turn. This
section is the Lean mirror: the gated forest's ROOT credential is the `Authorization.token` arm AND
its cap-authority leg is the REAL `AuthMode.token` (the windowed biscuit's attenuation caveats), NOT
the `.unchecked` admit-by-construction `mkAuth` pins. So the token gates the executor admission on
BOTH legs, witnessed non-vacuously each direction:

  * a VALID, in-scope token (genuine biscuit signature ∧ caveat context inside the granted window)
    is ADMITTED → the forest COMMITS;
  * a FORGED-signature token (the biscuit signature does not verify) is REJECTED by the WHO leg
    (`credentialValidG = false`) → `none`, whole-forest rollback;
  * an OVER-ATTENUATED token (the credential is presented in a context OUTSIDE its granted window —
    the biscuit's own attenuation caveats narrow it out) is REJECTED by the WHAT leg
    (`capAuthorityG = false`) → `none`, whole-forest rollback.

The two negatives are ORTHOGONAL (different gate legs), so neither is laundered by the other. This is
the executable face of "the token gates the executor, not the narration." -/

open Dregg2.Authority (Caveat Token TokenKind)

/-- The agent-facing biscuit credential's WHO arm: an `Authorization.token` whose biscuit signature
verifies under the reference kernel (`sig` echoes the issuer `key`). The Rust SubAgent presents the
encoded `eb2_…` biscuit; here the portal arm is `CryptoKernel.verify key sig` (`Crypto.Reference`:
`decide (key = sig)`), so a genuine credential's signature equals its issuer key. -/
def goodTokenCred : Authorization Dg Pf := .token 11 11

/-- A FORGED biscuit credential: the signature (`12`) does NOT verify against the issuer key (`11`).
The §8 portal WHO leg (`credentialValidG`) fail-closes — exactly the executor's `TokenAuthInvalid`. -/
def forgedTokenCred : Authorization Dg Pf := .token 11 12

/-- The windowed biscuit the agent carries: a root biscuit attenuated to the height window
`[100, 200]` — the Lean mirror of the SubAgent's biscuit scoped (via its Datalog/caveats) to exactly
the verbs/window the worker may invoke. Its `admits` is the meet of both caveats over the context's
`caveatCtx` (height). The starbridge `baseCapCtx.caveatCtx = 150` is INSIDE the window. -/
def agentToken : Token Cx Gw :=
  { kind := .biscuit
  , caveats := [ .local (fun h => decide (100 ≤ h)), .local (fun h => decide (h ≤ 200)) ] }

/-- The cap-context whose `caveatCtx` (height `150`) lands INSIDE the token's `[100,200]` window —
the in-scope presentation. (Everything else mirrors `baseCapCtx`.) -/
def tokenCtxInWindow : AuthContext Rq St Wt Label Rt Cx Gw := baseCapCtx

/-- The cap-context whose `caveatCtx` (height `50`) lands OUTSIDE the token's `[100,200]` window —
the over-attenuated presentation (the biscuit's own caveat narrows it out). -/
def tokenCtxOutOfWindow : AuthContext Rq St Wt Label Rt Cx Gw := { baseCapCtx with caveatCtx := 50 }

/-- **`mkAuthToken`** — a node-auth on the AGENT-FACING Token path: the WHO leg is the
`Authorization.token` biscuit credential (portal), and the WHAT leg is the REAL `AuthMode.token`
windowed biscuit (`agentToken`) — NOT the `.unchecked (Guard.all [])` that `mkAuth` pins. So the
token's attenuation actually gates the executor admission. The cap-CONTEXT is supplied (in/out of
window) so the same credential admits in-scope and rejects over-attenuated. -/
def mkAuthToken (cred : Authorization Dg Pf) (ctx : AuthContext Rq St Wt Label Rt Cx Gw)
    (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .token agentToken, capCtx := ctx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-- A VALID agent-token forest: genuine biscuit credential, in-window cap context. Balance-neutral
`emitEvent`, so the only gate that matters is the credential+attenuation. ADMITS. -/
def tokenOkForestG : DForest :=
  ⟨ mkAuthToken goodTokenCred tokenCtxInWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- A FORGED-signature agent-token forest: same in-window context, but the biscuit signature does not
verify. REJECTED by the WHO leg. -/
def tokenForgedForestG : DForest :=
  ⟨ mkAuthToken forgedTokenCred tokenCtxInWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- An OVER-ATTENUATED agent-token forest: genuine biscuit credential, but presented in a context
OUTSIDE the token's `[100,200]` window — the biscuit's own attenuation caveat narrows it out.
REJECTED by the WHAT leg (`capAuthorityG`). -/
def tokenOverAttenForestG : DForest :=
  ⟨ mkAuthToken goodTokenCred tokenCtxOutOfWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- **WHO leg — the genuine biscuit credential VERIFIES (PROVED).** The `Authorization.token` arm
routes through the §8 portal (`CryptoKernel.verify 11 11` = `decide (11 = 11)` = `true`). -/
theorem tokenOkForestG_credential_valid : credentialValidG tokenOkForestG.auth = true := by
  unfold tokenOkForestG mkAuthToken credentialValidG goodTokenCred
  decide

/-- **WHO leg — the FORGED biscuit credential FAILS (PROVED, the teeth).** The portal's
`CryptoKernel.verify 11 12` = `decide (11 = 12)` = `false`: a forged biscuit signature fail-closes
exactly as the executor's `TokenAuthInvalid`. NON-VACUOUS against the positive above. -/
theorem tokenForgedForestG_credential_invalid : credentialValidG tokenForgedForestG.auth = false := by
  unfold tokenForgedForestG mkAuthToken credentialValidG forgedTokenCred
  decide

/-- **WHAT leg — the in-window token's attenuation ADMITS (PROVED).** `AuthMode.token agentToken`
admits iff ALL the biscuit's caveats discharge on `caveatCtx = 150`: `100 ≤ 150 ∧ 150 ≤ 200`. This is
the token's OWN attenuation, gating the executor — not `.unchecked`. -/
theorem tokenOkForestG_what_admits : capAuthorityG tokenOkForestG.auth = true := by
  unfold tokenOkForestG mkAuthToken capAuthorityG agentToken tokenCtxInWindow baseCapCtx
  simp only [AuthModes.authModeAdmits, Dregg2.Authority.Token.admits, Dregg2.Authority.Caveat.ok,
    List.all_cons, List.all_nil]
  decide

/-- **WHAT leg — the OVER-ATTENUATED token's attenuation REJECTS (PROVED, the teeth).** Presented at
`caveatCtx = 50`, the biscuit's `100 ≤ h` caveat is FALSE, so `agentToken.admits = false` ⇒
`capAuthorityG = false`. The credential's OWN attenuation narrows it out of scope — the executor
rejects, not an out-of-band check. NON-VACUOUS against the in-window admit. -/
theorem tokenOverAttenForestG_what_rejects : capAuthorityG tokenOverAttenForestG.auth = false := by
  unfold tokenOverAttenForestG mkAuthToken capAuthorityG agentToken tokenCtxOutOfWindow baseCapCtx
  simp only [AuthModes.authModeAdmits, Dregg2.Authority.Token.admits, Dregg2.Authority.Caveat.ok,
    List.all_cons, List.all_nil]
  decide

/-- The valid agent-token forest's caveat leg discharges at `fma0` (`trueCaveat`). -/
theorem tokenOkForestG_caveats_fma0 : caveatsDischarged tokenOkForestG.auth fma0 = true := by
  unfold tokenOkForestG mkAuthToken caveatsDischarged trueCaveat chainGateG fma0
  simp only [List.all_cons, List.all_nil, Bool.and_true, GatedCaveat.holds, decide_eq_true_eq]
  norm_num

/-- The valid agent-token forest is not revoked at `fma0`. -/
theorem tokenOkForestG_revocation_fma0 : revocationGate tokenOkForestG.auth fma0 = true := by
  unfold tokenOkForestG mkAuthToken revocationGate fma0
  simp

/-- **`tokenOkForestG_gateOK` — the VALID agent token is ADMITTED by the full 4-leg gate (PROVED).**
WHO (biscuit verifies) ∧ WHAT (in-window attenuation admits) ∧ caveats ∧ not-revoked. The agent-facing
`Authorization::Token` gates the executor admission positively on the live path. -/
theorem tokenOkForestG_gateOK : gateOK tokenOkForestG.auth fma0 = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, tokenOkForestG_credential_valid, tokenOkForestG_what_admits,
             tokenOkForestG_caveats_fma0, tokenOkForestG_revocation_fma0]
  trivial

/-- **`tokenForgedForestG_gate_rejects` — the FORGED token is REJECTED by the gate (PROVED).** The WHO
leg fail-closes the conjunction. -/
theorem tokenForgedForestG_gate_rejects : gateOK tokenForgedForestG.auth fma0 = false := by
  unfold gateOK
  rw [tokenForgedForestG_credential_invalid]
  simp

/-- **`tokenOverAttenForestG_gate_rejects` — the OVER-ATTENUATED token is REJECTED by the gate
(PROVED).** The WHAT leg (the token's own attenuation) fail-closes the conjunction — orthogonal to the
forged case (the credential VERIFIES here; it is the attenuation that narrows it out). -/
theorem tokenOverAttenForestG_gate_rejects : gateOK tokenOverAttenForestG.auth fma0 = false := by
  unfold gateOK
  rw [tokenOverAttenForestG_what_rejects]
  simp [tokenOverAttenForestG_credential_valid_aux]
where
  /-- The over-attenuated forest's credential is the SAME genuine biscuit — it VERIFIES; only the
  attenuation rejects. (Used to show the rejection is the WHAT leg, not the WHO leg.) -/
  tokenOverAttenForestG_credential_valid_aux :
      credentialValidG tokenOverAttenForestG.auth = true := by
    unfold tokenOverAttenForestG mkAuthToken credentialValidG goodTokenCred
    decide

/-- **`tokenOkForestG_commits` — the VALID agent token COMMITS on the live `execFullForestG` path
(PROVED).** Not just `gateOK`: the whole gated forest runs and produces a post-state. This is the
end-to-end positive: an agent presenting a genuine, in-scope `Authorization::Token` has its turn
admitted by the verified executor. -/
theorem tokenOkForestG_commits : (execFullForestG fma0 tokenOkForestG).isSome := by
  have herase : (execFullForestA fma0 (eraseG tokenOkForestG)).isSome := by decide
  rcases Option.isSome_iff_exists.mp herase with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, tokenOkForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuthToken goodTokenCred tokenCtxInWindow [trueCaveat])
    (.emitEventA 0 0 0 0)).mpr ⟨tokenOkForestG_gateOK, hs'⟩
  simpa [hga]

/-- **`tokenForgedForestG_rolls_back` — the FORGED agent token does NOT commit (PROVED).** The gate
rejects ⇒ `execFullForestG = none` ⇒ whole-forest rollback. -/
theorem tokenForgedForestG_rolls_back : execFullForestG fma0 tokenForgedForestG = none := by
  have hgate : gateOK tokenForgedForestG.auth fma0 = false := tokenForgedForestG_gate_rejects
  unfold tokenForgedForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuthToken forgedTokenCred tokenCtxInWindow [trueCaveat])
            (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

/-- **`tokenOverAttenForestG_rolls_back` — the OVER-ATTENUATED agent token does NOT commit (PROVED).**
The token's own attenuation narrows it out of scope ⇒ `execFullForestG = none` ⇒ rollback. The
credential verified; the EXECUTOR ADMISSION still rejects on the attenuation. -/
theorem tokenOverAttenForestG_rolls_back : execFullForestG fma0 tokenOverAttenForestG = none := by
  have hgate : gateOK tokenOverAttenForestG.auth fma0 = false := tokenOverAttenForestG_gate_rejects
  unfold tokenOverAttenForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuthToken goodTokenCred tokenCtxOutOfWindow [trueCaveat])
            (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

-- The agent-facing `Authorization::Token` gates the EXECUTOR on the live path, both legs, both ways:
#guard (credentialValidG tokenOkForestG.auth)                       --  true  (genuine biscuit verifies)
#guard (credentialValidG tokenForgedForestG.auth) == false          --  false (forged signature)
#guard (capAuthorityG tokenOkForestG.auth)                          --  true  (in-window attenuation)
#guard (capAuthorityG tokenOverAttenForestG.auth) == false          --  false (over-attenuated)
#guard ((execFullForestG fma0 tokenOkForestG).isSome)               --  true  (VALID token ⇒ COMMITS)
#guard ((execFullForestG fma0 tokenForgedForestG).isSome) == false  --  false (forged ⇒ rollback)
#guard ((execFullForestG fma0 tokenOverAttenForestG).isSome) == false --  false (over-attenuated ⇒ rollback)

#assert_axioms tokenOkForestG_credential_valid
#assert_axioms tokenForgedForestG_credential_invalid
#assert_axioms tokenOkForestG_what_admits
#assert_axioms tokenOverAttenForestG_what_rejects
#assert_axioms tokenOkForestG_gateOK
#assert_axioms tokenForgedForestG_gate_rejects
#assert_axioms tokenOverAttenForestG_gate_rejects
#assert_axioms tokenOkForestG_commits
#assert_axioms tokenForgedForestG_rolls_back
#assert_axioms tokenOverAttenForestG_rolls_back

end StarbridgeGated

end Dregg2.Exec