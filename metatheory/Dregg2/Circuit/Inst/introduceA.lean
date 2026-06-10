/-
# Dregg2.Circuit.Inst.introduceA — the v2 (`EffectCommit2`) instance for the AUTHORITY-INTRODUCE effect
  `introduceA` (the Granovetter unattenuated held-cap copy).

`introduceA` is one of the THREE constructors of the AUTHORITY-UNATTENUATED family (`delegate` ·
`introduceA` · `validateHandoffA`), all DEFINITIONALLY the same chained primitive `recCDelegate` (see
`Spec.AuthorityUnattenuated.execFullA_introduceA_eq`, an `rfl`). The single touched kernel field is
`caps` (the cap table `Caps := Label → List Cap`): a committed `introduceA intro rec t` installs
`grant s.kernel.caps rec (heldCapTo s.kernel.caps intro t)` (the recipient's slot gains the
introducer's held `t`-conferring cap, NON-amplifying held-copy; every other slot whole), prepends ONE
authority receipt (`authReceipt intro`) to the log, and FREEZES the 16 non-`caps` kernel fields.

So this is a FUNCTION-FIELD instance, NEAR-IDENTICAL to the `burnA` template (`Inst/burnA.lean`), where
the touched component is `bal` — the SAME `funcComponent` shape (a whole-function injective digest,
the realizable Poseidon-CR bar of `cellLeafInjective`), the SAME growing log, the SAME bit-gated guard.
It differs ONLY in (1) the touched field is `caps` not `bal` (so a NEW `RestIffNoCaps` rest-frame
portal, the v1 `RestHashIffFrame` with `caps` omitted — the 1-line mirror of `RestIffNoBal`); (2) the
spec-predicted value is `recDelegateCaps s.kernel.caps intro rec t` (the `grant`-of-held-cap, a FULL
function equality on `caps`), (3) the guard is the Granovetter connectivity premise `delegateGuard`
(the introducer already holds a `t`-conferring cap), and (4) the receipt + bridge target are the
authority family's (`authReceipt`, `DelegateSpec` via `execFullA_introduceA_eq`).

THE VALIDATION: `introduceA_full_sound ⇒ DelegateSpec` THROUGH the framework. A satisfying v2 full-state
witness for `introduceE` proves the complete declarative `DelegateSpec` (the apex truth in
`Dregg2/Circuit/Spec/authorityunattenuated.lean`, whose executor corner is `recCDelegate_iff_spec` and
whose `introduceA` arm is `execFullA_introduceA_eq` / `execFullA_introduceA_iff_spec`). `DelegateSpec`'s
`caps` clause is the FULL function equality `s'.kernel.caps = recDelegateCaps s.kernel.caps intro rec t`,
so it fits `funcComponent`'s `postClause` EXACTLY (no subset/weakening — the apex full-function equality
IS the spec's `caps` clause).

ADDITIVE: imports `EffectCommit2` + the authority-unattenuated spec; edits NEITHER `EffectCommit2`/
`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`. Follows the `burnA` template
(`Inst/burnA.lean`) EXACTLY + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityunattenuated

namespace Dregg2.Circuit.Inst.IntroduceA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `burnA` template).

The authority spec exposes its guard as a `Prop` (`delegateGuard`, the Granovetter connectivity
premise `(s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true`), not a per-gate circuit, so
we commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`.
(Identical to `burnA`/`mintE`/`noteSpendE`; the bit gate is guard-agnostic.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoCaps` portal (the v1 `RestHashIffFrame` minus `caps`).

The realizable injective-rest-hash portal for the effect that touches the `caps` function-field: the
rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), OMITTING `caps` (the touched field of the
authority-unattenuated family). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the
omitted field from `bal` to `caps`. Carried Prop hypothesis (realizable — a Poseidon hash of a
canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `introduceA`/`delegate`/`validateHandoffA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `introduceE` instance (touched component = `caps`).

`introduceA` over `RecChainedState`: the touched component is the cap table `caps` (a `funcComponent`
whose digest is an injective whole-function hash — the realizable bar of `cellLeafInjective`); the log
GROWS by the authority receipt; the frame is the 16 non-`caps` kernel fields (`RestIffNoCaps`). -/

/-- The introduce effect arguments: the introducer (delegator), the recipient, and the target the
introduced cap confers an edge to. (The SAME `(del, rec, t)` shape as `DelegateSpec`.) -/
structure IntroduceArgs where
  intro : CellId
  recip : CellId
  t     : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The introduce guard as a `Prop` (the spec's `delegateGuard` — the Granovetter connectivity premise
on the introducer + target). -/
def introduceGuardProp (s : RecChainedState) (args : IntroduceArgs) : Prop :=
  delegateGuard s args.intro args.t

instance (s : RecChainedState) (args : IntroduceArgs) : Decidable (introduceGuardProp s args) := by
  unfold introduceGuardProp delegateGuard; exact inferInstanceAs (Decidable (_ = _))

/-- The introduce guard's witness generator: lay the single `propBit` column at wire `0`. -/
def introduceGuardEncode (s : RecChainedState) (args : IntroduceArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (introduceGuardProp s args) else 0

/-- The introduce guard sub-system: the single `propBit` gate. -/
def introduceGuardGates : ConstraintSystem := [cBitGuard]

/-- **`introduceGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem introduceGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied introduceGuardGates a ↔ satisfied introduceGuardGates b := by
  unfold satisfied introduceGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the `grant`-of-held-cap `recDelegateCaps s.kernel.caps intro rec t` (a FULL
function equality on `caps` — a tamper of any OTHER holder's cap-slot is REJECTED by injectivity, not
just "recipient gained the cap"). The SOLE structural difference from `burnA` (which predicts the `bal`
debit `recBalCredit … (-amt)`). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState IntroduceArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => recDelegateCaps s.kernel.caps args.intro args.recip args.t)

/-- **`introduceE`** — the `EffectSpec2` for `introduceA`, supplied to the v2 framework. -/
def introduceE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState IntroduceArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.intro :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := introduceGuardGates
  guardProp    := introduceGuardProp
  guardWidth   := 1
  guardEncode  := introduceGuardEncode
  guardLocal   := introduceGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `introduceE`. -/

/-- **`GuardDecodes2 (introduceE …)`** — the single bit gate on the guard witness decodes to
`delegateGuard`. -/
theorem introduceGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (introduceE D hD) := by
  intro s args s' hsat
  change satisfied introduceGuardGates (introduceGuardEncode s args s') at hsat
  show introduceGuardProp s args
  have hg := hsat cBitGuard (by simp [introduceGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, introduceGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (introduceE …)`** — `delegateGuard` encodes to the satisfied bit gate. -/
theorem introduceGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (introduceE D hD) := by
  intro s args s' hg
  show satisfied introduceGuardGates (introduceGuardEncode s args s')
  intro c hc
  simp only [introduceGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, introduceGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `introduceE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the `caps`-omitting
rest frame). -/
theorem introduceRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (introduceE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `DelegateSpec` bridge.

The framework's derived `apex` for `introduceE` is EXACTLY `DelegateSpec` instantiated at
`(args.intro, args.rec, args.t)`. The guard is `delegateGuard`; the component `postClause` is the FULL
`caps` function equality (`recDelegateCaps s.kernel.caps intro rec t` — so the apex full-function
equality IS the spec's `caps` clause, no subset/weakening); the log is the authority-receipt-prepended
chain; the `restFrame` is the 16 non-`caps` frame clauses. The spec's field order is `accounts cell
escrows nullifiers revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert
delegate delegations sealedBoxes` — VERBATIM the `restFrame` order, so both directions are a flat
re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_delegateSpec`** — the framework's derived `apex` for `introduceE` is EXACTLY
`DelegateSpec s args.intro args.rec args.t s'`. -/
theorem apex_iff_delegateSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState) :
    (introduceE D hD).apex s args s' ↔ DelegateSpec s args.intro args.recip args.t s' := by
  show (introduceGuardProp s args
        ∧ s'.kernel.caps = recDelegateCaps s.kernel.caps args.intro args.recip args.t
        ∧ s'.log = authReceipt args.intro :: s.log
        ∧ ((introduceE D hD).restFrame s.kernel s'.kernel))
       ↔ DelegateSpec s args.intro args.recip args.t s'
  unfold DelegateSpec introduceGuardProp introduceE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `introduceA_full_sound ⇒ DelegateSpec` through the framework. -/

/-- **`introduceA_full_sound` — the VALIDATION (introduce through the v2 framework).** A satisfying v2
full-state witness for `introduceE` proves the complete declarative `DelegateSpec` (the
authority-unattenuated apex). Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame),
`logHashInjective LH` (the growing log), `Function.Injective D` (the `caps` component's whole-function
digest — the realizable Poseidon-CR bar). CONCLUDES the bespoke `Spec.AuthorityUnattenuated.DelegateSpec`
THROUGH the generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the authority-introduce
triangle (whose executor corner is `execFullA_introduceA_iff_spec`, via `execFullA_introduceA_eq`). -/
theorem introduceA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s')) :
    DelegateSpec s args.intro args.recip args.t s' := by
  have hapex : (introduceE D hD).apex s args s' :=
    effect2_circuit_full_sound S (introduceE D hD)
      (introduceRestFrameDecodes S D hD hRest) hLog (introduceGuardDecodes D hD) s args s' h
  exact (apex_iff_delegateSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def introduceEWire : EffectSpec2 RecChainedState IntroduceArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := introduceGuardGates
  guardProp    := introduceGuardProp
  guardWidth   := 1
  guardEncode  := introduceGuardEncode
  guardLocal   := introduceGuardLocal
  guardWidth_le := by decide

def introduceAAirName : String := "dregg-introduceA-v2"

def introduceAEmitted : EmittedDescriptor := emittedEffect2 introduceAAirName introduceEWire

#guard introduceAEmitted.name == introduceAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms introduceGuardLocal
#assert_axioms introduceGuardDecodes
#assert_axioms introduceGuardEncodes
#assert_axioms apex_iff_delegateSpec
#assert_axioms introduceA_full_sound

end Dregg2.Circuit.Inst.IntroduceA
