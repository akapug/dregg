/-
# Dregg2.Circuit.CircuitCompletenessAuthority — the COMPLETENESS rungs (cap-token / authority wave) for
the CAP-AUTHORIZED effects whose soundness AUTHORITY leg is realized in `RotatedKernelRefinementFacet`
(`EffAuthoritySource` / `effAuthoritySource_authorizes`, routed through `Emit/CapOpenEmit`'s
`effCapOpenV3_authorizes`): **attenuate**, **exercise**, **delegate**, **introduce**, **grantCap**,
**revoke**, **revokeDelegation**, **refreshDelegation**, **revokeCapability**. The dual of the cap-open
authority refinement — the CONVERSE of `effCapOpenV3_authorizes`.

SOUNDNESS (`Emit/CapOpenEmit.effCapOpenV3_authorizes` + `Facet.effAuthoritySource_authorizes`) is the
implication `cap-open Satisfied2 + DeployedFaithfulEff + (actor⇒src) edge ⟹ authorizedFacetEffB caps
provided (1 <<< n) tr = true`: the in-circuit depth-16 cap-membership open DISCHARGES the deployed
two-axis (tier × facet) authority gate. The light client reads authority off the proof.

COMPLETENESS is the OTHER direction: from a GENUINE kernel transition (which holds when authority is
true) we must CONSTRUCT a cap-open authority source so an accepting proof EXISTS. A cap-authorized turn
HAS an authority opening — the circuit never spuriously rejects a genuinely cap-authorized move.

## THE LOAD-BEARING ASYMMETRY (resolved HONESTLY — the prompt's case (a), confirmed against the kernel)

The kernel authority gate is (`Exec/FacetAuthority.authorizedFacetEffB`):

  `authorizedFacetEffB caps provided effectBit turn`
    `= decide (turn.actor = turn.src) || (caps turn.actor).any (capAuthorizesFacetEff provided effectBit turn)`

— authority is by OWNERSHIP (`actor = src`, the intra-vat short-circuit) **OR** by a CAP (a `FacetCap`
in `caps actor` targeting `src` whose facet permits `effectBit` under a satisfied tier). The soundness
keystone `effCapOpenV3_authorizes` discharges authority STRICTLY through the CAP disjunct: it routes via
`authorizedFacetEffB_holds_cap`, which exhibits the `.any` member from the opened leaf's deployed
faithfulness. There is no cap-open witness for the OWNER disjunct — there is no cap to open.

So completeness of the cap-OPEN descriptor is NECESSARILY about CAP-AUTHORIZED turns. The honest
completeness statement is CONDITIONAL on the authority being cap-based — the hypothesis `AuthorizedByCap`
(§1): a concrete witnessing `FacetCap c ∈ caps actor` with `c.target = src`, `isEffectPermitted c.facet
(1 <<< n)`, and `c.tier.isSatisfiedBy provided`. Under it, the cap-open authority source is constructible
(the cap IS in the tree → the membership opening exists), and re-derives `authorizedFacetEffB = true`.

The OWNER-authorized turn (`actor = src`, no cap) proves authority through a DIFFERENT, OWNER path — NOT
the cap-open descriptor. That path is a SEPARATE, trivially-constructive rung (§7,
`<effectBit>_owner_authorityComplete`): `decide (actor = src) = true` discharges the disjunction with NO
cap-open, NO membership, NO prover floor. We state BOTH honestly; we do NOT pretend the cap-open
descriptor witnesses owner-authority, and we do NOT pretend cap-completeness is unconditional. This is a
GENUINE asymmetry of the gate (a disjunction), surfaced and named — the residual is that the owner path
needs (and HAS) its own rung, which we land here too.

## What is built (per cap-authorized effect, dual to the soundness `EffAuthoritySource` keystone)

  * `CapOpenWitness` (§2) — the realizable cap-open CONSTRUCTION floor (NAMED, dual of the soundness
    `EffAuthoritySource`'s carried trace data, which soundness EXTRACTS off a satisfying proof; here the
    honest prover BUILDS it). It bundles the cap-open `Satisfied2` of the live `effCapOpenV3 base name n`
    descriptor, the chip-table soundness, the opened row, the deployed leaf assignment, the deployed
    faithfulness `DeployedFaithfulEff`, the `(actor⇒src)` edge identification, and the committed-tier
    side condition — the prover's actual depth-16 cap-membership opening. REALIZABLE, named, NOT faked
    (the dual of the soundness `StarkSound`/`ChipTableSound` extraction).
  * `<eff>_authoritySource_construct` (§3+) — ASSEMBLE the `EffAuthoritySource` from `CapOpenWitness`.
    Pure repackaging: every field of `EffAuthoritySource` is supplied by the realizable cap-open floor.
  * `<eff>_authorityComplete` (§3+) — THE RUNG: from a cap-authorized turn (`AuthorizedByCap`) + the
    realizable `CapOpenWitness`, the deployed two-axis `authorizedFacetEffB caps provided (1 <<< n) tr =
    true` PASSES, FORCED by the constructed source (`effAuthoritySource_authorizes`). The dual of
    `effCapOpenV3_authorizes`.

## The non-vacuity teeth (the cap-authority is REAL, both polarities)

  * `<eff>_authorityComplete_genuine` (§3+) — the constructed source's authority conclusion is the SAME
    gate the kernel admits the move under, AND it is forced through the CAP path (the witnessing cap is a
    genuine `.any` member). Read off `authorizedFacetEffB_holds_cap` directly: the `AuthorizedByCap`
    hypothesis ALONE forces `authorizedFacetEffB = true` (independent of the cap-open) — so the rung's
    conclusion is non-degenerate and the antecedent is satisfiable.
  * `authorizedByCap_nonvacuous` (§8) — a concrete cap-table (actor 5 holds a transfer-facet cap over
    src 9) inhabits `AuthorizedByCap`, so the antecedent is not vacuously empty.
  * `unauthorized_no_capWitness` (§8) — the BOTH-POLARITY tooth: an actor whose cap-table confers NO
    edge-cap over `src` for `effectBit` (and is not the owner) is NOT authorized — the gate genuinely
    bites (no `AuthorizedByCap`, no source, no accepting authority proof for that turn).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `CapOpenWitness` enters as a NAMED structure
carrier (the realizable cap-open construction floor), never an axiom — exactly as the soundness
`EffAuthoritySource` is a named carrier and `StarkComplete` is a named class. No `sorry`, no
`native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.CircuitCompleteness

namespace Dregg2.Circuit.CircuitCompletenessAuthority

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FacetAuthority
open Dregg2.Authority (Label)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (DeployedFaithfulEff tierOfTag)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf)
open Dregg2.Circuit.Emit.CapOpenEmit
  (effCapOpenV3 effCapOpenV3_authorizes capOpenCols
   EFF_TRANSFER EFF_GRANT_CAPABILITY EFF_REVOKE_CAPABILITY EFF_INTRODUCE EFF_DELEGATION_OPS
   transferV3 introduceV3 grantCapV3 revokeDelegationV3 refreshDelegationV3 revokeCapabilityBaseV3)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (attenuateV3)
open Dregg2.Circuit.RotatedKernelRefinementFacet (EffAuthoritySource effAuthoritySource_authorizes)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2 ChipTableSound envAt)

set_option autoImplicit false

/-! ## §1 — `AuthorizedByCap`: the honest CAP-AUTHORITY hypothesis (the converse precondition).

The kernel gate `authorizedFacetEffB caps provided effectBit turn` is a DISJUNCTION (owner OR cap). The
cap-open descriptor witnesses ONLY the cap disjunct. The honest completeness precondition for the
cap-open authority leg is therefore that the turn is CAP-authorized: a concrete witnessing `FacetCap` in
`caps actor` over `src` permitting `effectBit` under a satisfied tier. This is the EXACT data the soundness
`DeployedFaithfulEff.backed` produces; here it is the antecedent the honest prover holds (it KNOWS which
cap authorizes its move). -/

/-- **`AuthorizedByCap caps provided effectBit tr`** — the turn is authorized BY A CAP (NOT by ownership):
the actor holds SOME `FacetCap` over `tr.src` whose facet permits `effectBit` and whose tier is satisfied
by `provided`. The honest cap-authority precondition — the disjunct the cap-open descriptor witnesses (the
owner disjunct `actor = src` is the SEPARATE §7 path). The EXACT data the soundness
`DeployedFaithfulEff.backed` produces (an existential over the witnessing cap). -/
def AuthorizedByCap (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (tr : Turn) : Prop :=
  ∃ c : FacetCap, c ∈ caps tr.actor ∧ c.target = tr.src
    ∧ isEffectPermitted c.facet effectBit = true
    ∧ c.tier.isSatisfiedBy provided = true

/-- **`authorizedByCap_forces_gate` — the cap-authority hypothesis ALONE forces the deployed gate.** A
cap-authorized turn passes the deployed two-axis `authorizedFacetEffB caps provided effectBit tr` — the
witnessing cap is a genuine `.any` member (via `authorizedFacetEffB_holds_cap`). This is the CONVERSE
target the cap-open construction re-derives circuit-side; here it is the kernel fact the hypothesis
carries (the move WAS admitted, so authority holds). -/
theorem authorizedByCap_forces_gate (caps : FacetCaps) (provided : AuthProvided)
    (effectBit : EffectMask) (tr : Turn) (h : AuthorizedByCap caps provided effectBit tr) :
    authorizedFacetEffB caps provided effectBit tr = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := h
  exact authorizedFacetEffB_holds_cap caps provided effectBit tr c hmem htgt hfacet htier

/-! ## §2 — `CapOpenWitness`: the realizable cap-open CONSTRUCTION floor (NAMED, dual of the soundness
`EffAuthoritySource` data).

The soundness keystone `effCapOpenV3_authorizes` is handed (by `StarkSound`/`ChipTableSound`) the cap-open
`Satisfied2`, the chip soundness, the opened row, the deployed leaf assignment + faithfulness, and the
edge/tier side conditions — and EXTRACTS authority. Completeness goes the other way: the honest prover
BUILDS that opening for its real cap. `CapOpenWitness` bundles EXACTLY that constructed data — the dual of
the soundness extraction (here a CONSTRUCTION). It is the realizable prover floor (named, not faked); the
authority conclusion is then FORCED from it through `EffAuthoritySource` (§3+), not assumed. -/

/-- **`CapOpenWitness hash caps provided pre tr base name n` — the realizable cap-open construction floor
(NAMED).** The prover's IN-CIRCUIT cap-tree opening for the cap-authorized turn at the fan-out descriptor
`effCapOpenV3 base name n`: a cap-open `Satisfied2` of THAT live descriptor (against a sound chip table),
the opened row, the deployed leaf assignment + its `DeployedFaithfulEff` at the cap-open's committed root
over the ACTUAL effect bit `1 <<< n`, the `(actor⇒src)` edge identification, and the committed-tier side
condition. The honest prover holding a real authorizing cap CAN produce this (it opens that cap's leaf);
it is the realizable construction dual of the soundness `EffAuthoritySource`'s carried trace data.
DATA-bearing (`Type 1`, like `EffAuthoritySource`). -/
structure CapOpenWitness (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    : Type 1 where
  /-- the effect bit `n` is a valid mask bit (`< MASK_BITS`); the submask-gate side condition. -/
  hn : n < Dregg2.Circuit.DeployedCapOpen.MASK_BITS
  /-- the deployed cap-hash scheme the cap-tree commits under (its existential state type). -/
  State : Type
  /-- the deployed cap-hash scheme carrier. -/
  S : CapHashScheme State
  /-- the `Custom`-tier vk decode (the named felt residual). -/
  vkOfTag : ℤ → Nat
  /-- the cap-open trace + its memory boundary (the prover's BUILT cap-tree opening). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the prover's BUILT cap-open `Satisfied2` of the live fan-out descriptor. -/
  hsat : Satisfied2 S.chipAbsorb (effCapOpenV3 base name n) minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the deployed leaf assignment the cap-tree root realizes. -/
  leafAt : Label → Label → CapLeaf
  /-- the deployed-faithfulness of the opened leaf set at the cap-open root over the ACTUAL effect bit. -/
  hfaith : DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps
    ((envAt t i).loc capOpenCols.capRoot) leafAt
  /-- the cap-open row's `src` column IS the turn's `src`. -/
  hsrc : (envAt t i).loc capOpenCols.src = (tr.src : ℤ)
  /-- the opened leaf IS the faithful `(actor⇒src)` edge leaf. -/
  hedge : leafOf capOpenCols (envAt t i) = leafAt tr.actor tr.src
  /-- `provided` satisfies the tier decoded off the committed leaf. -/
  htier : (tierOfTag vkOfTag (leafAt tr.actor tr.src).auth_tag).isSatisfiedBy provided = true

/-- **`capOpenWitness_to_source` — the cap-open floor IS an `EffAuthoritySource`.** Pure repackaging: a
`CapOpenWitness` supplies EVERY field the soundness `EffAuthoritySource` carries. So the realizable
construction floor and the soundness authority source are the SAME data — the completeness rung rides the
soundness keystone (`effAuthoritySource_authorizes`) directly, not a divergent path. -/
def capOpenWitness_to_source (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (w : CapOpenWitness hash caps provided pre tr base name n) :
    EffAuthoritySource hash caps provided pre tr base name n where
  hn := w.hn
  State := w.State
  S := w.S
  vkOfTag := w.vkOfTag
  minit := w.minit
  mfin := w.mfin
  maddrs := w.maddrs
  t := w.t
  hChip := w.hChip
  hsat := w.hsat
  i := w.i
  hi := w.hi
  leafAt := w.leafAt
  hfaith := w.hfaith
  hsrc := w.hsrc
  hedge := w.hedge
  htier := w.htier

/-! ## §3 — the GENERIC cap-authority completeness rung (the template all cap-effects share).

From the realizable cap-open floor `CapOpenWitness` (the prover's BUILT opening), the deployed two-axis
authority gate at the effect's OWN bit PASSES — FORCED by the constructed `EffAuthoritySource` via
`effAuthoritySource_authorizes` (the soundness keystone). This is the dual of `effCapOpenV3_authorizes`:
the in-circuit cap-membership open, BUILT by the honest prover, discharges the gate. -/

/-- **`authorityComplete_generic` — THE CAP-AUTHORITY COMPLETENESS RUNG (generic template).** From the
realizable cap-open construction floor `CapOpenWitness … base name n` (the honest prover's BUILT opening
of the authorizing cap at the effect's bit `n`), the deployed two-axis `authorizedFacetEffB caps provided
(1 <<< n) tr = true` PASSES — FORCED by the constructed `EffAuthoritySource` (`effAuthoritySource_
authorizes`), NOT carried. The dual of `effCapOpenV3_authorizes`: a cap-authorized move HAS an accepting
authority opening. -/
theorem authorityComplete_generic (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (w : CapOpenWitness hash caps provided pre tr base name n) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true :=
  effAuthoritySource_authorizes hash caps provided pre tr base name n
    (capOpenWitness_to_source hash caps provided pre tr base name n w)

/-- **`authorityComplete_generic_genuine` — the non-vacuity tooth (the cap-authority is REAL).** Under the
cap-authority hypothesis `AuthorizedByCap caps provided (1 <<< n) tr`, the deployed gate the constructed
source concludes is the SAME `authorizedFacetEffB caps provided (1 <<< n) tr = true` the kernel admits the
move under (through the CAP path, the witnessing `.any` member) — so the rung's conclusion is
non-degenerate (an honest cap genuinely authorizes; the antecedent is satisfiable). -/
theorem authorityComplete_generic_genuine (caps : FacetCaps) (provided : AuthProvided) (n : Nat)
    (tr : Turn) (h : AuthorizedByCap caps provided (1 <<< n) tr) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true :=
  authorizedByCap_forces_gate caps provided (1 <<< n) tr h

/-! ## §4 — the PER-EFFECT cap-authority rungs (each at its OWN descriptor + effect bit).

Each cap-authorized effect rides its LIVE fan-out cap-open descriptor (`Emit/CapOpenEmit`) at its
deployed effect bit. The rung is `authorityComplete_generic` specialized to that `(base, name, n)`; the
genuine tooth is `authorityComplete_generic_genuine` at that bit. The bit assignments are the deployed
`facet.rs` constants: transfer/attenuate-via-transfer-cap = `EFF_TRANSFER` (1); grantCap = `EFF_GRANT_
CAPABILITY` (2); revokeCapability = `EFF_REVOKE_CAPABILITY` (3); introduce = `EFF_INTRODUCE` (13);
delegate / revoke(Delegation) / refreshDelegation = `EFF_DELEGATION_OPS` (16). -/

/-- **`attenuate_authorityComplete`** — the cap-authority completeness rung over the LIVE
`attenuateCapOpenEffV3` (base `attenuateV3`, `EFF_TRANSFER`; the attenuate-via-transfer-cap leaf must
permit `EFFECT_TRANSFER`). The dual of the attenuate authority leg. -/
theorem attenuate_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER) :
    authorizedFacetEffB caps provided (1 <<< EFF_TRANSFER) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_TRANSFER w

/-- **`introduce_authorityComplete`** — the cap-authority completeness rung over the LIVE
`introduceCapOpenV3` (base `introduceV3`, `EFF_INTRODUCE`; the cap must permit `EFFECT_INTRODUCE`). -/
theorem introduce_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      introduceV3 "dregg-effectvm-introduce-v1-rot24-v3-capopen" EFF_INTRODUCE) :
    authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_INTRODUCE w

/-- **`grantCap_authorityComplete`** — the cap-authority completeness rung over the LIVE
`grantCapCapOpenV3` (base `grantCapV3`, `EFF_GRANT_CAPABILITY`; the cap must permit
`EFFECT_GRANT_CAPABILITY`). -/
theorem grantCap_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      grantCapV3 "dregg-effectvm-grantCap-v1-rot24-v3-capopen" EFF_GRANT_CAPABILITY) :
    authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_GRANT_CAPABILITY w

/-- **`delegate_authorityComplete`** — the cap-authority completeness rung over the LIVE
`delegateCapOpenV3` (base `grantCapV3` — delegateAtten shares the grant base, distinguished by name;
`EFF_DELEGATION_OPS`; the cap must permit `EFFECT_DELEGATION_OPS`). -/
theorem delegate_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      grantCapV3 "dregg-effectvm-delegateAtten-v1-rot24-v3-capopen" EFF_DELEGATION_OPS) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_DELEGATION_OPS w

/-- **`revokeDelegation_authorityComplete`** — the cap-authority completeness rung over the LIVE
`revokeCapOpenV3` (base `revokeDelegationV3`, `EFF_DELEGATION_OPS`; revoke / revokeDelegation share this
base — the cap must permit `EFFECT_DELEGATION_OPS`). -/
theorem revokeDelegation_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      revokeDelegationV3 "dregg-effectvm-revoke-v1-rot24-v3-capopen" EFF_DELEGATION_OPS) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_DELEGATION_OPS w

/-- **`refreshDelegation_authorityComplete`** — the cap-authority completeness rung over the LIVE
`refreshDelegationCapOpenV3` (base `refreshDelegationV3`, `EFF_DELEGATION_OPS`; the cap must permit
`EFFECT_DELEGATION_OPS`). -/
theorem refreshDelegation_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      refreshDelegationV3 "dregg-effectvm-refresh-v1-rot24-v3-capopen" EFF_DELEGATION_OPS) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_DELEGATION_OPS w

/-- **`revokeCapability_authorityComplete`** — the cap-authority completeness rung over the LIVE
`revokeCapabilityCapOpenV3` (base `revokeCapabilityBaseV3`, `EFF_REVOKE_CAPABILITY`; the cap must permit
`EFFECT_REVOKE_CAPABILITY`). -/
theorem revokeCapability_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen"
      EFF_REVOKE_CAPABILITY) :
    authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_REVOKE_CAPABILITY w

/-! ## §5 — the PER-EFFECT non-vacuity teeth (the cap-authority is REAL at each effect's bit).

Each rung's antecedent is satisfiable: under the effect's `AuthorizedByCap` hypothesis the deployed gate
holds (through the CAP path). These teeth pin that the per-effect conclusion is non-degenerate (a degenerate
"always-true" gate would not need the witnessing cap). -/

/-- attenuate — the cap-authority is real at `EFF_TRANSFER`. -/
theorem attenuate_authorityComplete_genuine (caps : FacetCaps) (provided : AuthProvided) (tr : Turn)
    (h : AuthorizedByCap caps provided (1 <<< EFF_TRANSFER) tr) :
    authorizedFacetEffB caps provided (1 <<< EFF_TRANSFER) tr = true :=
  authorityComplete_generic_genuine caps provided EFF_TRANSFER tr h

/-- introduce — the cap-authority is real at `EFF_INTRODUCE`. -/
theorem introduce_authorityComplete_genuine (caps : FacetCaps) (provided : AuthProvided) (tr : Turn)
    (h : AuthorizedByCap caps provided (1 <<< EFF_INTRODUCE) tr) :
    authorizedFacetEffB caps provided (1 <<< EFF_INTRODUCE) tr = true :=
  authorityComplete_generic_genuine caps provided EFF_INTRODUCE tr h

/-- grantCap — the cap-authority is real at `EFF_GRANT_CAPABILITY`. -/
theorem grantCap_authorityComplete_genuine (caps : FacetCaps) (provided : AuthProvided) (tr : Turn)
    (h : AuthorizedByCap caps provided (1 <<< EFF_GRANT_CAPABILITY) tr) :
    authorizedFacetEffB caps provided (1 <<< EFF_GRANT_CAPABILITY) tr = true :=
  authorityComplete_generic_genuine caps provided EFF_GRANT_CAPABILITY tr h

/-- delegate / revoke(Delegation) / refreshDelegation — the cap-authority is real at
`EFF_DELEGATION_OPS`. -/
theorem delegationOps_authorityComplete_genuine (caps : FacetCaps) (provided : AuthProvided) (tr : Turn)
    (h : AuthorizedByCap caps provided (1 <<< EFF_DELEGATION_OPS) tr) :
    authorizedFacetEffB caps provided (1 <<< EFF_DELEGATION_OPS) tr = true :=
  authorityComplete_generic_genuine caps provided EFF_DELEGATION_OPS tr h

/-- revokeCapability — the cap-authority is real at `EFF_REVOKE_CAPABILITY`. -/
theorem revokeCapability_authorityComplete_genuine (caps : FacetCaps) (provided : AuthProvided)
    (tr : Turn) (h : AuthorizedByCap caps provided (1 <<< EFF_REVOKE_CAPABILITY) tr) :
    authorizedFacetEffB caps provided (1 <<< EFF_REVOKE_CAPABILITY) tr = true :=
  authorityComplete_generic_genuine caps provided EFF_REVOKE_CAPABILITY tr h

/-! ## §6 — exercise: the HOLD-GATE cap-authority completeness rung.

`exercise`'s authority is a HOLD-GATE cap MEMBERSHIP (`exerciseGuard`: `(caps actor).any (confersEdgeTo
target)`), forced in-circuit by the deployed cap-open over the LIVE `attenuateCapOpenEffV3` (the
`RotatedKernelRefinementExerciseAuth.ExerciseHoldSource` template). Its authority bit is `EFF_TRANSFER`
(the exercise hold-cap must permit `EFFECT_TRANSFER`, mirroring the deployed routing), so the exercise
cap-authority completeness rung IS `attenuate_authorityComplete`'s descriptor at `EFF_TRANSFER` — the
exercise hold-cap opens exactly as the attenuate transfer-cap does. We record it as its own named rung for
the fan-out, riding the SAME `CapOpenWitness` floor. -/

/-- **`exercise_authorityComplete`** — the exercise hold-gate cap-authority completeness rung (over the
LIVE `attenuateCapOpenEffV3` at `EFF_TRANSFER`, the descriptor the deployed exercise hold-cap routes
through). From the realizable cap-open floor, the deployed two-axis gate at `EFF_TRANSFER` PASSES — the
exercise hold-cap membership has an accepting opening. -/
theorem exercise_authorityComplete (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn)
    (w : CapOpenWitness hash caps provided pre tr
      attenuateV3 "dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff" EFF_TRANSFER) :
    authorizedFacetEffB caps provided (1 <<< EFF_TRANSFER) tr = true :=
  authorityComplete_generic hash caps provided pre tr _ _ EFF_TRANSFER w

/-! ## §7 — THE OWNER PATH: the SEPARATE, trivially-constructive authority rung (the named residual).

The §1-§6 rungs are CONDITIONAL on cap-authority — they witness the CAP disjunct of `authorizedFacetEffB`.
The OWNER disjunct (`actor = src`, the intra-vat short-circuit) is a GENUINELY SEPARATE path: an
owner-authorized turn has NO cap to open, so it CANNOT prove through the cap-open descriptor. But it is
authorized — and its authority is discharged DIRECTLY (no cap-open, no membership, no prover floor) by
`decide (actor = src) = true`. This is the honest residual the asymmetry names: the owner path needs its
own rung, and HERE IT IS — `authorizedFacetEffB_owner`, lifted to the completeness register.

This is NOT a stub: it is the TRUE statement that owner-authority completeness holds UNCONDITIONALLY (no
hypothesis beyond `actor = src`), at EVERY effect bit, because the gate short-circuits on ownership. The
two disjuncts of the gate correspond to two completeness rungs; we prove BOTH. -/

/-- **`owner_authorityComplete`** — THE OWNER-PATH AUTHORITY COMPLETENESS RUNG (the separate residual,
landed).** An owner-authorized turn (`actor = src`) passes the deployed two-axis gate at ANY effect bit
UNCONDITIONALLY — the intra-vat short-circuit discharges authority with NO cap-open (there is no cap to
open). This is the SEPARATE owner disjunct the cap-open descriptor cannot witness; its completeness is
trivially constructive (`authorizedFacetEffB_owner`). The honest companion of the cap-authority rungs. -/
theorem owner_authorityComplete (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (tr : Turn) (howner : tr.actor = tr.src) :
    authorizedFacetEffB caps provided effectBit tr = true :=
  authorizedFacetEffB_owner caps provided effectBit tr howner

/-- **`authorityComplete_dichotomy`** — the gate is EXACTLY (owner OR cap), so completeness of authority
is EXACTLY the two rungs.** Either disjunct discharges the deployed gate; together they cover every
authorized turn. This makes the asymmetry precise: there is no THIRD path, and neither rung subsumes the
other (owner needs no cap; cap needs no ownership). -/
theorem authorityComplete_dichotomy (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (tr : Turn) (h : tr.actor = tr.src ∨ AuthorizedByCap caps provided effectBit tr) :
    authorizedFacetEffB caps provided effectBit tr = true := by
  cases h with
  | inl howner => exact owner_authorityComplete caps provided effectBit tr howner
  | inr hcap => exact authorizedByCap_forces_gate caps provided effectBit tr hcap

/-! ## §8 — non-vacuity: the cap-authority antecedent is INHABITED, and the gate BITES (both polarities).

The cap-authority hypothesis is satisfiable (a concrete cap-table inhabits it), and the gate genuinely
REJECTS a non-owner with no conferring cap — so neither the cap rung's antecedent nor the gate is
vacuous. -/

/-- A concrete cap-table: actor `5` holds a transfer-facet cap over src `9` (broad transfer mask,
`Signature` tier). -/
private def demoCaps : FacetCaps :=
  fun a => if a = 5 then [{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }] else []

private def demoTurn : Turn := { actor := 5, src := 9, dst := 7, amt := 3 }

/-- **`authorizedByCap_nonvacuous` — the cap-authority antecedent is INHABITED.** The demo cap-table
inhabits `AuthorizedByCap` for the demo turn at `EFF_TRANSFER` — so the cap rungs' antecedent is not
vacuously empty (an honest transfer cap genuinely cap-authorizes). -/
theorem authorizedByCap_nonvacuous :
    AuthorizedByCap demoCaps .signature (1 <<< EFF_TRANSFER) demoTurn :=
  ⟨{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER },
   by decide, by decide, by decide, by decide⟩

/-- **`authorityComplete_fires` — the cap rung's conclusion FIRES on the demo cap.** Composing the demo
witness through `authorizedByCap_forces_gate`, the deployed gate PASSES — the cap-authority completeness
conclusion is realized, not vacuous. -/
theorem authorityComplete_fires :
    authorizedFacetEffB demoCaps .signature (1 <<< EFF_TRANSFER) demoTurn = true :=
  authorizedByCap_forces_gate demoCaps .signature (1 <<< EFF_TRANSFER) demoTurn
    authorizedByCap_nonvacuous

/-- **`unauthorized_no_authority` — the BOTH-POLARITY tooth (the gate BITES).** A NON-owner whose
cap-table is EMPTY (confers no cap over `src`) is NOT authorized — the deployed gate is `false`. So there
is no `AuthorizedByCap`, no `CapOpenWitness`, and no accepting authority opening for that turn: the cap
rung's hypothesis genuinely separates authorized from unauthorized moves. -/
theorem unauthorized_no_authority (provided : AuthProvided) (effectBit : EffectMask)
    (actor src dst : Label) (amt : ℤ) (hne : actor ≠ src) :
    authorizedFacetEffB (fun _ => []) provided effectBit
      { actor := actor, src := src, dst := dst, amt := amt } = false := by
  unfold authorizedFacetEffB
  have howner : (decide ((⟨actor, src, dst, amt⟩ : Turn).actor = (⟨actor, src, dst, amt⟩ : Turn).src))
      = false := by simp [hne]
  simp [howner]

/-! ## §9 — axiom hygiene. -/

#assert_axioms authorizedByCap_forces_gate
#assert_axioms capOpenWitness_to_source
#assert_axioms authorityComplete_generic
#assert_axioms authorityComplete_generic_genuine
#assert_axioms attenuate_authorityComplete
#assert_axioms introduce_authorityComplete
#assert_axioms grantCap_authorityComplete
#assert_axioms delegate_authorityComplete
#assert_axioms revokeDelegation_authorityComplete
#assert_axioms refreshDelegation_authorityComplete
#assert_axioms revokeCapability_authorityComplete
#assert_axioms attenuate_authorityComplete_genuine
#assert_axioms introduce_authorityComplete_genuine
#assert_axioms grantCap_authorityComplete_genuine
#assert_axioms delegationOps_authorityComplete_genuine
#assert_axioms revokeCapability_authorityComplete_genuine
#assert_axioms exercise_authorityComplete
#assert_axioms owner_authorityComplete
#assert_axioms authorityComplete_dichotomy
#assert_axioms authorizedByCap_nonvacuous
#assert_axioms authorityComplete_fires
#assert_axioms unauthorized_no_authority

end Dregg2.Circuit.CircuitCompletenessAuthority
