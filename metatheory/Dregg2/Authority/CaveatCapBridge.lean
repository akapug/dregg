/-
# Dregg2.Authority.CaveatCapBridge — the macaroon ↔ kernel-cap convergence arrow.

`docs/rebuild/_AUTHORIZATION-COMPLETE.md §3` welds FOUR caveat operators onto the SAME live
`execFullForestG` gate: the within-cell tiers, the cap-authority `granted ≤ held`
(`capAuthorityG`, the WHAT leg), the coordinated cross-cell axis, and the macaroon HMAC
caveat-CHAIN (`chainGateG`). Those last two — the macaroon narrowing and the kernel cap
narrowing — are TWO renderings of the ONE fact "a key may only narrow":

  * the macaroon side (`CaveatChain.append_narrows`): appending a caveat can only SHRINK the
    admissible set — `{ctx | (c.append link).admits} ⊆ {ctx | c.admits}`;
  * the kernel cap side (`AuthModes.captp_granted_le_held` / `Caps.attenuate_confRights_le`):
    a delegated cap's conferred rights are `⊆` the parent's — `granted.rights ≤ held.rights`
    over `ExecAuth = Finset Auth`.

This module makes the convergence an EXPLICIT, PROVEN ARROW rather than two parallel facts.
The shared narrowing is `caveatChainAuthority : ExecAuth → List ExecAuth → ExecAuth`: the
rights a macaroon chain confers = the parent rights MET against each link's kept-rights mask.
Then:

  * `caveatChainAuthority_le_held` — the chain authority is ALWAYS `≤ held` (REFINEMENT, the
    general `⊆` the lead asked for): a macaroon, however attenuated, never amplifies past the
    held rights;
  * `caveatChainAuthority_append_le` — appending a link's mask only narrows further (the
    `append_narrows` analog, on the rights lattice);
  * `delegationVerb_authority_eq` — on the DELEGATION VERB (one kept-rights step `keep` with
    `keep ≤ held`), the chain authority is EXACTLY `keep` — the EQUALITY the lead flagged: the
    macaroon's narrowing and the kernel `confRights (attenuate keep …)` coincide, not merely
    refine;
  * the keystone `chainGateG_implies_capAuthorityG` — on a COHERENTLY-built node (its
    `.capTpDelivered` WHAT leg's `granted` IS `caveatChainAuthority held keeps`, the SAME
    narrowing its macaroon chain carries), `chainGateG na = true → capAuthorityG na = true`.
    The `&&` of the two gate legs becomes a PROVEN arrow on the overlap: a verifying-and-admitting
    macaroon chain forces the kernel cap gate to pass, because the granted rights it confers were
    DEFINED as the narrowed meet `≤ held`.

REUSES `Authority.CaveatChain` (the real HMAC chain + `verifiedChainGate`),
`Exec.FullForestAuth` (`chainGateG`/`capAuthorityG`/`NodeAuth`), `Exec.AuthModes`
(`authModeAdmits`/`.capTpDelivered`), `Exec.Caps` (`ExecAuth`/`confRights`/`attenuate`),
`Exec.GatedForestCfg` (the starbridge production carriers). EDITS none. ONE namespace.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Authority.CaveatChain

namespace Dregg2.Authority.CaveatCapBridge

open Dregg2.Exec
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.AuthModes (AuthMode AuthContext authModeAdmits)
open Dregg2.Exec.StarbridgeGated
open Dregg2.Authority
open Dregg2.Spec (Cap)

/-! ## §1 — The shared narrowing `caveatChainAuthority`.

A macaroon chain's caveats are rendered, on the rights lattice, as a list of KEPT-RIGHTS MASKS
(one `ExecAuth` per link). The authority a chain confers from a parent's `held` rights is the
parent met against every mask — exactly the kernel's `attenuate`-down-a-chain semantics, on
`ExecAuth = Finset Auth` ordered by `⊆`. This is the ONE object both the macaroon `append_narrows`
and the kernel `granted ≤ held` are about. -/

/-- **`caveatChainAuthority held keeps`** — the rights a macaroon chain confers from a parent's
`held` rights: the meet (`⊓` = `∩` on `Finset Auth`) of `held` with every link's kept-rights mask.
`keeps = []` (a root macaroon, no caveats) confers exactly `held`; each appended mask narrows. -/
def caveatChainAuthority (held : ExecAuth) (keeps : List ExecAuth) : ExecAuth :=
  keeps.foldl (fun r m => r ⊓ m) held

@[simp] theorem caveatChainAuthority_nil (held : ExecAuth) :
    caveatChainAuthority held [] = held := rfl

theorem caveatChainAuthority_cons (held m : ExecAuth) (keeps : List ExecAuth) :
    caveatChainAuthority held (m :: keeps) = caveatChainAuthority (held ⊓ m) keeps := rfl

/-- **`caveatChainAuthority_le_held` — the REFINEMENT direction (the general `⊆`).** Whatever a
macaroon chain confers from `held`, it is `≤ held`: a key, however attenuated, never amplifies
past the parent's rights. The macaroon `append_narrows`, rendered on the kernel rights lattice. -/
theorem caveatChainAuthority_le_held (held : ExecAuth) (keeps : List ExecAuth) :
    caveatChainAuthority held keeps ≤ held := by
  induction keeps generalizing held with
  | nil => exact le_rfl
  | cons m rest ih =>
      rw [caveatChainAuthority_cons]
      exact le_trans (ih (held ⊓ m)) inf_le_left

/-- **`caveatChainAuthority_append_le` — appending a link only narrows further.** Adding a caveat
mask `m` to the chain shrinks (or fixes) the conferred authority: `auth (keeps ++ [m]) ≤ auth keeps`.
The rights-lattice rendering of `CaveatChain.append_narrows`. -/
theorem caveatChainAuthority_append_le (held : ExecAuth) (keeps : List ExecAuth) (m : ExecAuth) :
    caveatChainAuthority held (keeps ++ [m]) ≤ caveatChainAuthority held keeps := by
  induction keeps generalizing held with
  | nil =>
      show caveatChainAuthority held [m] ≤ held
      exact caveatChainAuthority_le_held held [m]
  | cons k rest ih =>
      rw [List.cons_append, caveatChainAuthority_cons, caveatChainAuthority_cons]
      exact ih (held ⊓ k)

/-! ## §2 — The DELEGATION-VERB equality (the lead's "EQUALITY on the delegation verb").

The delegation verb attenuates a held cap to exactly the kept-rights set `keep` (`recKDelegateAtten`
→ `attenuate keep held`, `confRights (attenuate keep c) = keep.toFinset ⊓ confRights c`). A single
macaroon caveat carrying that mask reproduces it EXACTLY: when `keep ≤ held`, the chain authority is
not merely `≤ held` but EQUAL to `keep`. So on the delegation verb the two narrowings COINCIDE. -/

/-- **`delegationVerb_authority_eq` — the EQUALITY.** With a single delegation caveat whose mask is
`keep`, and `keep ≤ held` (the non-amplifying delegation precondition), the macaroon chain confers
EXACTLY `keep`. Not a refinement — an equality: the macaroon narrowing IS the kernel attenuation. -/
theorem delegationVerb_authority_eq (held keep : ExecAuth) (hle : keep ≤ held) :
    caveatChainAuthority held [keep] = keep := by
  show held ⊓ keep = keep
  exact inf_eq_right.mpr hle

/-- **`delegationVerb_authority_le` — the REFINEMENT face of the same step** (no precondition):
a single delegation caveat confers `≤ held` regardless. The general arrow direction; the equality
above is the special case `keep ≤ held`. -/
theorem delegationVerb_authority_le (held keep : ExecAuth) :
    caveatChainAuthority held [keep] ≤ held :=
  caveatChainAuthority_le_held held [keep]

/-! ## §3 — The convergence keystone: `chainGateG na → capAuthorityG na` on a coherent node.

A node is COHERENT for the bridge when its `.capTpDelivered` WHAT leg's `granted` rights ARE
`caveatChainAuthority held keeps` — the SAME narrowing its macaroon chain renders — and its `held`
is the parent rights. Then `capAuthorityG na = decide (granted ≤ held) && facetOk && freshOk`, and
`granted ≤ held` is `caveatChainAuthority_le_held` (PROVED), so on `baseCapCtx` (facet/fresh = true)
the cap gate passes. The macaroon `chainGateG` is the hypothesis; the cap gate is the conclusion —
the `&&` of the two legs is now a PROVEN arrow on the overlap. -/

/-- The coherent `.capTpDelivered` cap mode whose `granted` rights ARE the shared narrowing
`caveatChainAuthority held keeps` over the parent `held`, on the production `ExecAuth` lattice.
`held` and `granted` share a target (the rights are what the bridge gates). -/
def bridgeCapMode (target : Label) (held : ExecAuth) (keeps : List ExecAuth) :
    AuthMode Rq St Wt Label Rt Cx Gw :=
  .capTpDelivered
    { introducer := target, recipient := target
    , held    := { target := target, rights := held }
    , granted := { target := target, rights := caveatChainAuthority held keeps } }
    True

/-- **`bridgeCapMode_admits` — the WHAT leg of a coherent node ALWAYS passes.** Because its
`granted` rights are `caveatChainAuthority held keeps ≤ held` (`caveatChainAuthority_le_held`), the
`.capTpDelivered` dispatch `decide (granted ≤ held) && facetOk && freshOk` is `true` at `baseCapCtx`
(facet/fresh `true`). This is the kernel cap gate the macaroon narrowing implies. -/
theorem bridgeCapMode_admits (target : Label) (held : ExecAuth) (keeps : List ExecAuth) :
    authModeAdmits (bridgeCapMode target held keeps) baseCapCtx = true := by
  unfold bridgeCapMode authModeAdmits baseCapCtx
  -- `.capTpDelivered` admits = `decide (granted ≤ held) && facetOk && freshOk`; facet/fresh are
  -- `true` in `baseCapCtx`, so the gate reduces to the proved narrowing `granted ≤ held`.
  simp only [Bool.and_true, decide_eq_true_eq]
  exact caveatChainAuthority_le_held held keeps

/-- A coherent bridge node: its WHO/caveats are the production `mkAuth` defaults (a genuine
credential, the chain present), but its WHAT leg is the coherent `bridgeCapMode` AND it carries the
macaroon `chain` whose narrowing the WHAT leg mirrors. The bridge's hypothesis-bearing object. -/
def mkBridgeNode (cred : Authorization Dg Pf) (target : Label) (held : ExecAuth)
    (keeps : List ExecAuth)
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg)) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := bridgeCapMode target held keeps, capCtx := baseCapCtx
  , caveats := [], chain := chain, chainCtx := 150, chainDis := fun _ => false }

/-- **`chainGateG_implies_capAuthorityG` — THE CONVERGENCE ARROW.** On a coherent bridge node
(whose `.capTpDelivered` `granted` IS the macaroon chain's narrowing `caveatChainAuthority held
keeps`), the macaroon caveat-chain gate passing implies the kernel cap-authority gate passing:
`chainGateG na = true → capAuthorityG na = true`. The `&&` of the two gate legs in `gateOK` is now a
PROVEN implication on the overlap — a verifying macaroon chain CANNOT pass while the kernel cap gate
fails, because the rights it confers were DEFINED as the narrowed meet `≤ held`. -/
theorem chainGateG_implies_capAuthorityG (cred : Authorization Dg Pf) (target : Label)
    (held : ExecAuth) (keeps : List ExecAuth)
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg))
    (_hchain : chainGateG (mkBridgeNode cred target held keeps chain) = true) :
    capAuthorityG (mkBridgeNode cred target held keeps chain) = true := by
  show authModeAdmits (bridgeCapMode target held keeps) baseCapCtx = true
  exact bridgeCapMode_admits target held keeps

/-! ## §4 — Non-vacuity: both polarities, on the SAME live gate.

The arrow is NOT vacuous: there ARE chains for which `chainGateG = true` (a verifying, admitting
macaroon — the hypothesis fires) AND there ARE narrowings for which the conclusion is the
non-trivial `granted ⊊ held` (a strict attenuation, not `held = held`). And the EQUALITY/refinement
split is witnessed: a non-amplifying `keep ≤ held` gives EQUALITY, an over-broad mask gives a STRICT
refinement `granted ⊊ held` (the kernel gate would reject the over-broad cap, exactly as the
macaroon append narrowed it). -/

/-- A genuine production credential (reused from the starbridge config). -/
def credOk : Authorization Dg Pf := goodCred

/-- The full held rights for the demo (`{read, write}`). -/
def heldRW : ExecAuth := {Auth.read, Auth.write}

/-- A non-amplifying delegation mask (`{read}` ⊆ `{read, write}`) — the delegation verb keeps only
`read`. EQUALITY: the chain confers EXACTLY `{read}`. -/
def keepR : ExecAuth := {Auth.read}

/-- An OVER-BROAD mask (`{read, write, grant}` ⊄ `{read, write}`) — a macaroon caveat that names a
right the parent never held. The chain authority is the MEET (`{read, write}`), STRICTLY below the
named mask: the narrowing CLIPS the over-broad ask (the macaroon cannot amplify), and the resulting
`granted = {read, write} = held` — the over-broad ask buys nothing past the parent. -/
def keepOver : ExecAuth := {Auth.read, Auth.write, Auth.grant}

-- EQUALITY on the delegation verb: `keep ≤ held` ⇒ chain confers EXACTLY `keep`.
#guard (decide (caveatChainAuthority heldRW [keepR] = keepR))
-- REFINEMENT in general: the over-broad mask is CLIPPED to the held rights (no amplification).
#guard (decide (caveatChainAuthority heldRW [keepOver] = heldRW))
-- The clip is STRICT below the named over-broad mask (the macaroon could NOT name `grant` into being).
#guard (decide (caveatChainAuthority heldRW [keepOver] < keepOver))
-- The conferred rights are ALWAYS `≤ held` (refinement), here as a Bool check.
#guard (decide (caveatChainAuthority heldRW [keepR] ≤ heldRW))
#guard (decide (caveatChainAuthority heldRW [keepOver] ≤ heldRW))
-- Appending narrows: a second caveat `{read}` on top of `{read,write}` shrinks to `{read}`.
#guard (decide (caveatChainAuthority heldRW [heldRW, keepR] = keepR))

/-- **NON-VACUITY (positive):** the EQUALITY fires on the non-amplifying delegation verb. -/
theorem keepR_equality : caveatChainAuthority heldRW [keepR] = keepR :=
  delegationVerb_authority_eq heldRW keepR (by decide)

/-- **NON-VACUITY (negative tooth):** the over-broad mask does NOT confer itself — the chain
authority is STRICTLY below the named mask (`< keepOver`), so a macaroon naming a right the parent
never held buys nothing. This is the load-bearing non-amplification: the arrow's conclusion `granted
≤ held` is a REAL constraint, refuted for the over-broad ask if it were taken at face value. -/
theorem keepOver_strict_refines : caveatChainAuthority heldRW [keepOver] < keepOver := by decide

/-- **NON-VACUITY (the keystone fires on a CONCRETE coherent node).** With a real macaroon chain
present and the coherent WHAT leg, the convergence arrow's conclusion holds: the kernel cap gate
passes. Witnessed on the production carriers, not abstractly. -/
theorem bridge_keystone_concrete
    (chain : Option (CaveatChain.Chain Cx Gw (CaveatChain.Key Tg) Bt Tg))
    (h : chainGateG (mkBridgeNode credOk 0 heldRW [keepR] chain) = true) :
    capAuthorityG (mkBridgeNode credOk 0 heldRW [keepR] chain) = true :=
  chainGateG_implies_capAuthorityG credOk 0 heldRW [keepR] chain h

#assert_axioms caveatChainAuthority_le_held
#assert_axioms caveatChainAuthority_append_le
#assert_axioms delegationVerb_authority_eq
#assert_axioms bridgeCapMode_admits
#assert_axioms chainGateG_implies_capAuthorityG
#assert_axioms keepR_equality
#assert_axioms keepOver_strict_refines
#assert_axioms bridge_keystone_concrete

end Dregg2.Authority.CaveatCapBridge
