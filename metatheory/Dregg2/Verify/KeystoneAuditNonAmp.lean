/-
# Dregg2.Verify.KeystoneAuditNonAmp — the NON-AMPLIFICATION family keystone-audit (the EXEMPLAR).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the 8
`EffectsAuthority.*_non_amplifying` keystones — the most load-bearing AUTHORITY claim in the assurance
case (guarantee A: "no effect confers more authority than was held"). Each is the apex of one
authority-conferring mouth (introduce / attenuate / refresh / revokeDelegation / dropRef / exercise /
setPermissions / validateHandoff). The leaf-spec linter (`LoadBearingLint`) cannot audit these — they
are THEOREMS, not spec/gate pairs — so the keystone-audit's two checks bite instead:

  [1] NON-VACUITY — each keystone carries a `*_satisfiable` companion (in `EffectsAuthority §11`) that
      EXERCISES its conclusion on a concrete instance (the keystone fires; its hypotheses are jointly
      satisfiable — not vacuous), and
  [2] TEETH — each carries a `*_teeth` companion REFUTING an amplifying attempt
      (`amplifying_grant_rejected`-routed), so the keystone DISCRIMINATES (it is not `:= True`).

Both companions are `#assert_axioms`-clean in `EffectsAuthority`, so the audit's axiom-hygiene gate
(check [0] on the keystone + the cleanliness of each companion) bites. `#keystone_audit` THROWS on any
FAIL, so this module is a CI gate: a non-amp keystone that loses its non-vacuity or its teeth (e.g. an
impl weakening toward `True`, caught complementarily by the `NONAMP-WEAKEN` canary mutator) makes this
module RED.

The mutation half of the discipline is `scripts/mutation-canary.sh NONAMP-WEAKEN` (weakens
`IsNonAmplifying` toward `True`, requires this family to go RED). Together they are the in-band (this
module) + out-of-band (the canary) teeth the leaf discipline already has, now extended to the apex
keystones.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Exec.EffectsAuthority
import Dregg2.Exec.AuthModes

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditNonAmp

/-! ## §1 — TAG the 8 non-amplification keystones with their companions.

We tag via re-pinning aliases (`@[load_bearing_keystone …] theorem … := <the keystone>`) so the
attribute attaches the satisfiability + teeth companions WITHOUT editing `EffectsAuthority`'s keystone
declarations themselves (which carry their own `#assert_axioms` pins and must stay the canonical
home). Each alias is definitionally the keystone; the tag carries its `*_satisfiable` / `*_teeth`. -/

open Dregg2.Exec.EffectsAuthority
open Dregg2.Exec (RecChainedState attenuate confersEdgeTo)
open Dregg2.Authority (Auth Label capAuthConferred)
open Dregg2.Spec (execGraph ExecRights)

-- (1) INTRODUCE
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.introduce_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.introduce_non_amplifying_teeth]
theorem introduce_non_amplifying_KS (held : ECap) (keep : List Auth) :
    IsNonAmplifying held (attenuate keep held) :=
  introduce_non_amplifying held keep

-- (2) ATTENUATE
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.attenuate_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.attenuate_non_amplifying_teeth]
theorem attenuate_non_amplifying_KS (keep : List Auth) (c : ECap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  attenuate_non_amplifying keep c

-- (3) REFRESH
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.refresh_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.refresh_non_amplifying_teeth]
theorem refresh_non_amplifying_KS (keep : List Auth) (c : ECap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  refresh_non_amplifying keep c

-- (4) REVOKE-DELEGATION
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.revokeDelegation_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.revokeDelegation_non_amplifying_teeth]
theorem revokeDelegation_non_amplifying_KS (s : RecChainedState) (holder target : Label)
    (h : Label) (c : Dregg2.Spec.Cap Label ExecRights)
    (hpost : execGraph (revokeDelegationStep s holder target).kernel.caps h c) :
    execGraph s.kernel.caps h c :=
  revokeDelegation_non_amplifying s holder target h c hpost

-- (5) DROP-REF
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.dropRef_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.dropRef_non_amplifying_teeth]
theorem dropRef_non_amplifying_KS (s : RecChainedState) (holder target : Label)
    (h : Label) (c : Dregg2.Spec.Cap Label ExecRights)
    (hpost : execGraph (dropRefStep s holder target).kernel.caps h c) :
    execGraph s.kernel.caps h c :=
  dropRef_non_amplifying s holder target h c hpost

-- (6) EXERCISE
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.exercise_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.exercise_non_amplifying_teeth]
theorem exercise_non_amplifying_KS {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps
      ∧ ∃ held : ECap, held ∈ s.kernel.caps actor ∧ confersEdgeTo target held = true
          ∧ IsNonAmplifying held held :=
  exercise_non_amplifying h

-- (7) SET-PERMISSIONS
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.setPermissions_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.setPermissions_non_amplifying_teeth]
theorem setPermissions_non_amplifying_KS {old new : Label → Bool}
    (h : NarrowsGate old new) (l : Label) (hadmit : new l = true) : old l = true :=
  setPermissions_non_amplifying h l hadmit

-- (8) VALIDATE-HANDOFF
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.EffectsAuthority.validateHandoff_non_amplifying_satisfiable
    teeth := Dregg2.Exec.EffectsAuthority.introduce_non_amplifying_teeth]
theorem validateHandoff_non_amplifying_KS {CellId Rights : Type*}
    [SemilatticeInf Rights] [OrderTop Rights]
    (cert : Dregg2.Exec.CapTP.HandoffCert CellId Rights)
    (G : Dregg2.Spec.Graph CellId Rights) (consents : CellId → Prop) (attested : Prop)
    (hv : Dregg2.Exec.CapTP.HandoffValid cert G consents attested) :
    cert.granted.rights ≤ cert.held.rights :=
  validateHandoff_non_amplifying cert G consents attested hv

/-! ## §2 — RUN the audit (the CI gate over the non-amp family).

`#keystone_audit_tagged` sweeps the 8 tagged keystones above and THROWS if any fails its non-vacuity or
teeth check. Each `#keystone_audit` below is the per-keystone gate (it ALSO throws on FAIL), printed so
the report shows the family is covered.

The validateHandoff keystone's `teeth` reuses `introduce_non_amplifying_teeth` — handoff IS a
Granovetter introduce (`handoff_is_introduce`), so the SAME `amplifying_grant_rejected` refutation is its
discriminating instance (a handoff conferring more than held is rejected by the same predicate). -/

#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.introduce_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.attenuate_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.refresh_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.revokeDelegation_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.dropRef_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.exercise_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.setPermissions_non_amplifying_KS
#keystone_audit Dregg2.Verify.KeystoneAuditNonAmp.validateHandoff_non_amplifying_KS

-- the WHOLE-FAMILY sweep (the CI gate): throws if ANY tagged non-amp keystone loses its discipline.
#keystone_audit_tagged

/-! ## §3 — axiom-hygiene over the re-pinned aliases (kernel-triple clean). -/

#assert_axioms introduce_non_amplifying_KS
#assert_axioms attenuate_non_amplifying_KS
#assert_axioms refresh_non_amplifying_KS
#assert_axioms revokeDelegation_non_amplifying_KS
#assert_axioms dropRef_non_amplifying_KS
#assert_axioms exercise_non_amplifying_KS
#assert_axioms setPermissions_non_amplifying_KS
#assert_axioms validateHandoff_non_amplifying_KS

end Dregg2.Verify.KeystoneAuditNonAmp
