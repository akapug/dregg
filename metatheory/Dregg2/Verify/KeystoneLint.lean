/-
# Dregg2.Verify.KeystoneLint — the `@[load_bearing_keystone]` THEOREM-integrity audit.

The leaf-spec linter (`Dregg2.Verify.LoadBearingLint`) audits a `@[load_bearing]` *specification* — a
`Prop`-valued admissibility predicate / full-state relation — against its implementation GATE
(import-boundary + isDefEq-not-gate + non-vacuity-companion). That is the right discipline for a SPEC.

But the assurance case's apex (`Dregg2.AssuranceCase`) does not rest on the leaf specs alone: each of
its five guarantees is discharged by a small DAG of apex KEYSTONES — `EffectsAuthority.*_non_amplifying`,
`AuthModes.{captp,bearer,token}_sound`, `Argus.Receipt.*`, `RecursiveAggregation.*`, the unfoolability
apex — and a keystone is a THEOREM (a relation / implication), not a spec/gate pair. The leaf linter's
`isDefEq spec gate` check is MEANINGLESS for a theorem (a theorem has no "gate" it could collapse to).
The integrity questions for a load-bearing THEOREM are different, and this module audits them:

  1. **NON-VACUITY (satisfiable hypotheses + exercised conclusion).** A `*_sound : accept → ∃ genuine`
     is VACUOUSLY true if `accept` is never satisfiable. The keystone-audit requires a companion
     `satisfiable` witness: a NAMED, axiom-clean theorem proving the keystone's hypotheses are jointly
     SATISFIABLE on a concrete instance AND its conclusion is EXERCISED there (the non-amp keystones'
     `*_satisfiable` — `IsNonAmplifying` HOLDS on a real held cap). Existence + `sorry`/axiom-cleanliness
     are checked (the linter cannot read intent, but a vacuous keystone cannot carry a witness whose
     conclusion is its own non-vacuous instance — the operational proxy, same as the leaf linter's).

  2. **TEETH (the predicate DISCRIMINATES — not `:= True`).** A keystone whose conclusion is `True`
     (or holds for every input) constrains NOTHING. The audit requires a companion `teeth` witness: a
     NAMED, axiom-clean theorem REFUTING the keystone's conclusion on a hostile instance (an AMPLIFYING
     grant is REJECTED — `amplifying_grant_rejected`-style). A proof that the conclusion is non-trivially
     FALSE somewhere is the operational proof that proving the keystone constrains the code.

The MUTATION half of the discipline (a mutation of the impl / a consumed leaf that reds the keystone)
is the canary's job (`scripts/mutation-canary.sh`, the `NONAMP-WEAKEN` mutator), not this elaboration-
time command — a mutation tooth is an out-of-band falsification experiment, not a property of one
environment. This command is the IN-BAND half: it ASSERTS each tagged keystone carries its
satisfiability + teeth companions, both axiom-clean.

`#keystone_audit K (satisfiable := W) (teeth := T)` audits ONE keystone; `@[load_bearing_keystone
satisfiable := W teeth := T]` tags it; `#keystone_audit_tagged` sweeps the tagged corpus and THROWS on
any failure (a usable CI gate). Pure rejector — it can only report, never close a goal.
-/
import Lean
import Dregg2.Tactics

open Lean Elab Command Meta

namespace Dregg2.Verify.KeystoneLint

/-! ## §1 — the two checks for a load-bearing THEOREM. -/

structure CheckResult where
  pass   : Bool
  reason : String

/-- CHECK 1 — NON-VACUITY: the `satisfiable` companion exists and is `sorry`/axiom-clean. A keystone
`H → C` is vacuous if `H` is unsatisfiable; the companion is a NAMED theorem that satisfies `H` on a
concrete instance AND exercises `C` there. We check existence + axiom-cleanliness (a `sorryAx` leak ⇒ a
fake witness). With no companion supplied, we try the `<K>_satisfiable` naming convention; FAIL if
neither is found. -/
def checkSatisfiable (keystone : Name) (satisfiable? : Option Name) : MetaM CheckResult := do
  let env ← getEnv
  let candidate : Name := satisfiable?.getD (keystone.appendAfter "_satisfiable")
  match env.find? candidate with
  | none =>
    return { pass := false
             reason := s!"no satisfiability witness `{candidate}` — a keystone with no concrete \
               instance satisfying its hypotheses AND exercising its conclusion may be vacuously true" }
  | some _ =>
    let axs ← collectAxioms candidate
    let bad := axs.filter fun a => !Dregg2.cleanAxioms.contains a
    if bad.isEmpty then
      return { pass := true
               reason := s!"satisfiability witness `{candidate}` present + axiom-clean (the keystone \
                 fires on a concrete instance — its hypotheses are jointly satisfiable, not vacuous)" }
    else
      return { pass := false
               reason := s!"satisfiability witness `{candidate}` depends on non-kernel axioms \
                 {bad.toList} (a `sorryAx` here ⇒ the witness is fake)" }

/-- CHECK 2 — TEETH: the `teeth` companion exists and is `sorry`/axiom-clean. A keystone whose
conclusion is `:= True` constrains nothing; the companion is a NAMED theorem REFUTING the conclusion on
a hostile instance (an amplifying grant rejected). We check existence + axiom-cleanliness. With no
companion supplied, we try the `<K>_teeth` naming convention; FAIL if neither is found. -/
def checkTeeth (keystone : Name) (teeth? : Option Name) : MetaM CheckResult := do
  let env ← getEnv
  let candidate : Name := teeth?.getD (keystone.appendAfter "_teeth")
  match env.find? candidate with
  | none =>
    return { pass := false
             reason := s!"no teeth witness `{candidate}` — a keystone with no refuted hostile \
               instance may be `:= True` (constrains nothing); a load-bearing keystone must DISCRIMINATE" }
  | some _ =>
    let axs ← collectAxioms candidate
    let bad := axs.filter fun a => !Dregg2.cleanAxioms.contains a
    if bad.isEmpty then
      return { pass := true
               reason := s!"teeth witness `{candidate}` present + axiom-clean (a hostile instance — \
                 e.g. an amplifying grant — is REFUTED, so the keystone is two-valued, not `:= True`)" }
    else
      return { pass := false
               reason := s!"teeth witness `{candidate}` depends on non-kernel axioms {bad.toList} \
                 (a `sorryAx` here ⇒ the witness is fake)" }

/-- CHECK 0 — the keystone itself exists and is `sorry`/axiom-clean (a load-bearing keystone resting on
a leaked axiom is not load-bearing — it is faked-green). The leaf linter audits a SPEC (which may be a
`def`); here the subject IS a theorem, so we additionally pin its OWN axiom hygiene. -/
def checkKeystoneClean (keystone : Name) : MetaM CheckResult := do
  let env ← getEnv
  match env.find? keystone with
  | none => return { pass := false, reason := s!"keystone `{keystone}` not found in environment" }
  | some _ =>
    let axs ← collectAxioms keystone
    let bad := axs.filter fun a => !Dregg2.cleanAxioms.contains a
    if bad.isEmpty then
      return { pass := true, reason := "keystone is axiom-clean (kernel triple only)" }
    else
      return { pass := false
               reason := s!"keystone depends on non-kernel axioms {bad.toList} (faked-green)" }

/-! ## §2 — the audit driver + report. -/

structure AuditKeystone where
  keystone     : Name
  satisfiable? : Option Name := none
  teeth?       : Option Name := none

/-- Run all three checks on one keystone and return (overall, lines). -/
def runAudit (a : AuditKeystone) : MetaM (Bool × Array String) := do
  let c0 ← checkKeystoneClean a.keystone
  let c1 ← checkSatisfiable a.keystone a.satisfiable?
  let c2 ← checkTeeth a.keystone a.teeth?
  let mark (c : CheckResult) := if c.pass then "PASS" else "FAIL"
  let overall := c0.pass && c1.pass && c2.pass
  let lines := #[
    s!"  [0] keystone axiom-hygiene    : {mark c0} — {c0.reason}",
    s!"  [1] non-vacuity (satisfiable) : {mark c1} — {c1.reason}",
    s!"  [2] teeth (discriminates)     : {mark c2} — {c2.reason}",
    s!"  OVERALL: {if overall then "PASS (non-vacuous + discriminating + clean)" else "FAIL (vacuous / toothless / faked — see above)"}"]
  return (overall, lines)

/-! ## §3 — the `@[load_bearing_keystone]` attribute. -/

structure KeystoneEntry where
  satisfiable? : Option Name := none
  teeth?       : Option Name := none
  deriving Inhabited

initialize keystoneExt :
    SimplePersistentEnvExtension (Name × KeystoneEntry) (Std.HashMap Name KeystoneEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, e) => m.insert n e
    addImportedFn := fun ess => Id.run do
      let mut m : Std.HashMap Name KeystoneEntry := {}
      for es in ess do for (n, e) in es do m := m.insert n e
      return m }

syntax (name := loadBearingKeystoneAttr)
  "load_bearing_keystone" (" satisfiable " ":=" ident)? (" teeth " ":=" ident)? : attr

initialize registerBuiltinAttribute {
  name := `loadBearingKeystoneAttr
  descr := "marks a declaration as a load-bearing APEX KEYSTONE (a theorem) for the keystone-integrity audit"
  add := fun decl stx _kind => do
    let sat? ← match stx with
      | `(attr| load_bearing_keystone satisfiable := $s $[teeth := $_]?) =>
          some <$> (liftCommandElabM <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo s)
      | _ => pure none
    let teeth? ← match stx with
      | `(attr| load_bearing_keystone $[satisfiable := $_]? teeth := $t) =>
          some <$> (liftCommandElabM <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo t)
      | _ => pure none
    modifyEnv fun env =>
      keystoneExt.addEntry env (decl, { satisfiable? := sat?, teeth? := teeth? }) }

/-! ## §4 — the commands. -/

/-- `#keystone_audit K (satisfiable := W)? (teeth := T)?` — audit ONE keystone. Prints the report and
FAILS (throws) if the overall verdict is FAIL, so it is a usable CI gate. -/
syntax (name := keystoneAuditCmd)
  "#keystone_audit" ident (" satisfiable " ":=" ident)? (" teeth " ":=" ident)? : command

elab_rules : command
  | `(command| #keystone_audit $k $[satisfiable := $s?]? $[teeth := $t?]?) => do
    let keystone ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo k
    let mut sat?   ← s?.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let mut teeth? ← t?.mapM fun t => liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    -- Fall back to the `@[load_bearing_keystone]` attribute table when an explicit companion is not
    -- given inline, so a TAGGED keystone audits with its tagged companions under the bare command too.
    if sat?.isNone || teeth?.isNone then
      if let some e := (keystoneExt.getState (← getEnv)).get? keystone then
        if sat?.isNone then sat? := e.satisfiable?
        if teeth?.isNone then teeth? := e.teeth?
    let (overall, lines) ← liftTermElabM <|
      (runAudit { keystone, satisfiable? := sat?, teeth? := teeth? }).run'
    let report := s!"keystone audit — {keystone}\n" ++ String.intercalate "\n" lines.toList
    if overall then logInfo report else throwError report

/-- `#keystone_audit_report K …` — same checks, but ALWAYS `logInfo` (never throws). For surveying a
keystone known to lack a companion without failing the build. -/
syntax (name := keystoneAuditReportCmd)
  "#keystone_audit_report" ident (" satisfiable " ":=" ident)? (" teeth " ":=" ident)? : command

elab_rules : command
  | `(command| #keystone_audit_report $k $[satisfiable := $s?]? $[teeth := $t?]?) => do
    let keystone ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo k
    let sat?   ← s?.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let teeth? ← t?.mapM fun t => liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let (_overall, lines) ← liftTermElabM <|
      (runAudit { keystone, satisfiable? := sat?, teeth? := teeth? }).run'
    logInfo <| s!"keystone audit — {keystone}\n" ++ String.intercalate "\n" lines.toList

/-- `#keystone_audit_tagged` — sweep every `@[load_bearing_keystone]`-tagged keystone, auditing each
with its attached `satisfiable?`/`teeth?`. Throws if ANY fails (CI gate over the tagged corpus). -/
elab "#keystone_audit_tagged" : command => do
  let env ← getEnv
  let m := keystoneExt.getState env
  let entries := m.toList
  if entries.isEmpty then
    logWarning "#keystone_audit_tagged: no @[load_bearing_keystone] declarations found"
    return
  let mut anyFail := false
  let mut report := s!"#keystone_audit_tagged — {entries.length} tagged keystone(s)\n"
  for (keystone, e) in entries do
    let (overall, lines) ← liftTermElabM <|
      (runAudit { keystone, satisfiable? := e.satisfiable?, teeth? := e.teeth? }).run'
    report := report ++ s!"\n• {keystone}\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    unless overall do anyFail := true
  if anyFail then throwError report else logInfo report

end Dregg2.Verify.KeystoneLint
