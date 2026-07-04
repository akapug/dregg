/-
# Dregg2.Verify.KeystoneAuditAuthModes — the AUTH-MODE family keystone-audit (guarantee A, the
authorization half).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the load-bearing
`AuthModes.*_sound` keystones — dregg1's six authorization modes, each routing to a different soundness
obligation, all pinned in `AssuranceCase`'s authority guarantee (`captp_granted_le_held`, `captp_sound`,
`bearer_sound`, `token_sound`, plus the per-mode `custom_sound`). Each is a THEOREM (`admit ⟹ the
abstract authority object holds`), not a spec/gate pair, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — each keystone carries a `*_satisfiable` companion (in `AuthModes.Demo`, §6½/§6¾)
      that EXERCISES its conclusion on a concrete admitting instance (a `dfa` predicate discharged, a
      windowed biscuit admitted, an identity handoff conferring non-amplifyingly) — the hypotheses are
      jointly satisfiable, not vacuous; and
  [2] TEETH — each carries a `*_teeth` companion REFUTING the predicate on a hostile instance: the
      `nonMembership` kind the registry never installs is fail-closed (`custom`), a height outside the
      caveat window is rejected (`token`/`bearer`), and — the discriminating CORE — an AMPLIFYING handoff
      cert (`granted = true ⋬ false = held` over the two-point `Bool` rights lattice) is order-REFUSED
      (`captp_granted_le_held_teeth`). The Unit lattice in `Demo` makes the rights gate vacuous, so the
      captp teeth lives over `Bool`, the smallest lattice where amplification is expressible AND refused.

The `captp_granted_le_held` teeth is the load-bearing one: it is precisely the attenuation check
dregg1's `verify_captp_delivered` FAILS to perform, and the teeth proves our dispatcher's gate is
two-valued (an amplifying grant cannot pass), not `:= True`.

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate over the auth-mode family.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Exec.AuthModes

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditAuthModes

/-! ## §1 — TAG the auth-mode keystones with their companions.

We tag via re-pinning aliases (`@[load_bearing_keystone …] theorem …_KS … := <the keystone>`) so the
attribute attaches the satisfiability + teeth companions WITHOUT editing `AuthModes`'s keystone
declarations (which carry their own `#assert_axioms` pins and stay the canonical home). Each alias is
definitionally the keystone. -/

open Dregg2.Exec.AuthModes
open Dregg2.Laws (Verifiable Discharged)
open Dregg2.Spec (Guard Cap confers Graph Introduce)
open Dregg2.Authority (Token Discharges)
open Dregg2.Authority.Predicate (WitnessedKind)
open Dregg2.Exec.CapTP (HandoffCert HandoffValid)

variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable [Verifiable Stmt Wit]

-- (1) CUSTOM — witnessed-predicate dispatch.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.AuthModes.Demo.custom_sound_satisfiable
    teeth := Dregg2.Exec.AuthModes.Demo.custom_sound_teeth]
theorem custom_sound_KS (kind : WitnessedKind)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.custom kind) c = true) :
    @Discharged Stmt Wit (customSeam c.registry kind) c.customStmt (c.wit c.customStmt) :=
  custom_sound kind c h

-- (2) TOKEN — biscuit/macaroon caveat evaluation.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.AuthModes.Demo.token_sound_satisfiable
    teeth := Dregg2.Exec.AuthModes.Demo.token_sound_teeth]
theorem token_sound_KS (tok : Token Ctx Gateway)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.token tok) c = true) :
    Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway)
      c.caveatCtx (tok, c.discharges) :=
  token_sound tok c h

-- (3) BEARER — delegation-proof chain (non-amplifying conferral edge + token discharge).
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.AuthModes.Demo.bearer_sound_satisfiable
    teeth := Dregg2.Exec.AuthModes.Demo.bearer_sound_teeth]
theorem bearer_sound_KS (held granted : Cap CellId Rights) (tok : Token Ctx Gateway)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.bearer held granted tok) c = true) :
    confers held granted
      ∧ Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway)
          c.caveatCtx (tok, c.discharges) :=
  bearer_sound held granted tok c h

-- (4) CAPTP — the headline non-amplification (`granted ≤ held`, the check dregg1's Rust misses).
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.AuthModes.Demo.captp_granted_le_held_satisfiable
    teeth := Dregg2.Exec.AuthModes.CapTpTeeth.captp_granted_le_held_teeth]
theorem captp_granted_le_held_KS (cert : HandoffCert CellId Rights) (attested : Prop)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.capTpDelivered cert attested) c = true) :
    cert.granted.rights ≤ cert.held.rights :=
  captp_granted_le_held cert attested c h

-- (5) CAPTP-SOUND — admission + handoff premises ⟹ the `Introduce` step + non-amplification.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.AuthModes.Demo.captp_sound_satisfiable
    teeth := Dregg2.Exec.AuthModes.CapTpTeeth.captp_granted_le_held_teeth]
theorem captp_sound_KS (cert : HandoffCert CellId Rights) (attested : Prop)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (hv : HandoffValid cert c.graph c.consents attested)
    (h : authModeAdmits (.capTpDelivered cert attested) c = true) :
    Introduce c.graph c.consents cert.introducer cert.recipient cert.held cert.granted
        (cert.post c.graph)
      ∧ cert.granted.rights ≤ cert.held.rights :=
  captp_sound cert attested c hv h

/-! ## §2 — RUN the audit (the CI gate over the auth-mode family).

The `captp_sound` keystone reuses `captp_granted_le_held_teeth` for its teeth — the SAME amplifying-cert
order-refusal is its discriminating instance (a handoff conferring more than held cannot pass the
dispatcher's gate, so `captp_sound`'s admission hypothesis is never met by an amplifier). -/

#keystone_audit Dregg2.Verify.KeystoneAuditAuthModes.custom_sound_KS
#keystone_audit Dregg2.Verify.KeystoneAuditAuthModes.token_sound_KS
#keystone_audit Dregg2.Verify.KeystoneAuditAuthModes.bearer_sound_KS
#keystone_audit Dregg2.Verify.KeystoneAuditAuthModes.captp_granted_le_held_KS
#keystone_audit Dregg2.Verify.KeystoneAuditAuthModes.captp_sound_KS

/-! ## §3 — axiom-hygiene over the re-pinned aliases (kernel-triple clean). -/

#assert_axioms custom_sound_KS
#assert_axioms token_sound_KS
#assert_axioms bearer_sound_KS
#assert_axioms captp_granted_le_held_KS
#assert_axioms captp_sound_KS

end Dregg2.Verify.KeystoneAuditAuthModes
