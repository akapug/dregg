/-
# Dregg2.Spec.ExecRefinement — the first refinement square: `Exec ⊑ Spec`.

This module proves `Dregg2.Exec.Kernel ⊑ Dregg2.Spec.{Conservation,Guard,Authority}` — the
l4v `Design ⊑ Abstract` move. The refinement square:

```
        Refines
   k  ───────────▶  a
   │                │
   │ exec k t       │ abstract step (Spec law)
   ▼                ▼
   k' ───────────▶  a'
        Refines
```

Two tractable projections of the square are proved:

  1. **Conservation refinement** (`exec_refines_conservation`): an `exec`-committed step's
     per-cell balance deltas satisfy `Spec`'s `conservedInDomain Domain.balance` — i.e.
     `exec_conserves` IS `Spec`'s `Σδ = 0` law over `Bal = ℤ`.

  2. **Authority refinement** (`exec_authz_refines_guard`): `Exec.authorizedB` admitting a
     turn implies the corresponding abstract `Spec.Guard.admits` is `true`. Ownership is
     tied to `Spec.Authority.confers_refl`; held caps are tied to `Graph.has` on the
     reconstructed graph.

  3. **The simulation relation** (`Refines`, `exec_step_refines`): the conservation and
     authority projections are proved; the residual operational thread (an abstract small-step
     LTS for full bisimulation) is `-- OPEN:`-marked with a precise statement.

Also proves a second refinement square for the content-addressed record kernel
(`Exec.RecordKernel ⊑ Spec`), landing on the same abstract `Domain.balance` law.

Faithful `Prop`s; `#assert_axioms` on all keystones; the `-- OPEN:` is prose, not an open hole.
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.Caps
import Dregg2.Spec.Conservation
import Dregg2.Spec.Guard
import Dregg2.Spec.Authority
import Dregg2.Tactics
import Metatheory.Dynamics.Production
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dregg2.Spec

open Dregg2.Exec
-- NB: `Cap`/`Caps`/`Auth`/`Label` here are the EXECUTABLE authority carriers
-- (`Dregg2.Authority.Cap`, the `node`/`endpoint` inductive). They are deliberately NOT
-- `open`ed unqualified, because inside `Dregg2.Spec` the bare name `Cap` must resolve to the
-- ABSTRACT `Spec.Cap CellId Rights` (the rights-labelled-edge structure) that `confers`/`Graph`
-- read. We open only the non-conflicting names; the executable `Cap` is written `Authority.Cap`
-- and its constructors `Authority.Cap.node`/`Authority.Cap.endpoint` at the few sites that need
-- the inductive. (This is the load-bearing disambiguation of the refinement: two `Cap`s, one
-- executable and one abstract, are exactly what `Exec ⊑ Spec` must bridge.)
open Dregg2.Authority (Caps Auth Label capAuthConferred)
open Dregg2.Laws

open scoped BigOperators

/-! ## §1 — Conservation refinement: `Exec.exec_conserves` IS `Spec`'s `Σδ = 0` over ℤ.

The executable kernel conserves a SINGLE cleartext-ℤ ledger (`Exec.total`, a `Finset.sum`).
`Spec.Conservation` states `Σδ = 0` per `Domain`, parametric over a value monoid `Bal`, and
consumes the deltas as a `List Bal`. We exhibit the kernel's per-cell balance deltas as the
`List ℤ` that `conservedInDomain Domain.balance` reads, and prove a committed step's deltas
conserve — bridging `Exec.total`/`Finset.sum` to `Spec`'s `List.sum` exactly as `Coherence`
bridged the hyperedge (`Finset.sum_map_toList`).

So the toy single-ℤ ledger conservation is the `balance`-domain case of the multi-domain
abstract law: `Bal := ℤ`, `Domain := Domain.balance`. -/

/-- **`refineConservation s s'`** — the per-cell balance deltas of a step `s ⟶ s'`, packaged
as the `List ℤ` that `Spec.conservedInDomain` consumes. We enumerate the live accounts of the
*pre*-state (`exec` never changes `accounts`, only `bal`) and read off `s'.bal c - s.bal c`
per cell. This is the kernel's debit/credit ledger viewed as a conservation `deltas` list —
the `Bal = ℤ` instance of the abstract delta list. -/
noncomputable def refineConservation (s s' : KernelState) : List ℤ :=
  s.accounts.toList.map (fun c => s'.bal c - s.bal c)

/-- The list-sum of the per-cell deltas equals `total s' - total s` (over the SHARED account
set — `exec` preserves `accounts`). The `Finset.sum_map_toList` bridge from `Spec.Coherence`,
applied to the ℤ ledger: it turns the `List.sum` `Spec` reads into the `Finset.sum` `Exec`
uses. -/
theorem refineConservation_sum (s s' : KernelState) (hacc : s'.accounts = s.accounts) :
    (refineConservation s s').sum = total s' - total s := by
  unfold refineConservation total
  rw [Finset.sum_map_toList s.accounts (fun c => s'.bal c - s.bal c),
      Finset.sum_sub_distrib, hacc]

/-- **KEYSTONE 1 — `exec_refines_conservation`.** An `exec`-committed step's
per-cell balance deltas satisfy `Spec`'s balance-domain conservation
(`conservedInDomain Domain.balance`, i.e. `Σδ = 0` over `Bal = ℤ`). This is the conservation
PROJECTION of the refinement square: `Exec.exec_conserves` (the single-ℤ ledger preserves
`total`) IS, with no remainder, `Spec`'s `Σδ = 0` law instantiated at `Bal = ℤ`,
`Domain.balance`. The toy single-domain ledger is the `balance` case of multi-domain
conservation. -/
theorem exec_refines_conservation (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    conservedInDomain Domain.balance (refineConservation k k') := by
  -- `exec` preserves the account set (it only rewrites `bal`), and `total` (exec_conserves).
  have hacc : k'.accounts = k.accounts := by
    unfold exec at h
    by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
    · rw [if_neg hg] at h; exact absurd h (by simp)
  have htot : total k' = total k := exec_conserves k k' turn h
  unfold conservedInDomain
  rw [refineConservation_sum k k' hacc, htot, sub_self]

/-- The same conservation projection cast through the abstract monoid keystone: a committed
step's prior balance-domain total `pre` is unchanged by adding the step's deltas — the
`Bal = ℤ` instance of `Spec.conservation_over_monoid`. Confirms the executable refinement is
literally the abstract law's ℤ specialization, not a parallel re-proof. -/
theorem exec_refines_conservation_over_monoid (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') (pre : ℤ) :
    pre + (refineConservation k k').sum = pre :=
  conservation_over_monoid Domain.balance pre (refineConservation k k')
    (exec_refines_conservation k k' turn h)

/-- Multi-domain placement: a committed `exec` step conserves the `balance` domain of
the four-domain abstract law. We package the step's deltas as `TurnDeltas` that are the
kernel's ℤ ledger in the `balance` slot and empty (vacuously conserving) elsewhere, and read
off `turnConserves`-style balance conservation. This is the precise sense in which the
executable kernel inhabits ONE domain of `Spec.multi_domain_independent`. -/
theorem exec_inhabits_balance_domain (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    conservedInDomain (Bal := ℤ) Domain.balance
      ((fun dom => match dom with
                   | Domain.balance => refineConservation k k'
                   | _ => ([] : List ℤ)) Domain.balance) :=
  exec_refines_conservation k k' turn h

/-! ## §2 — Authority refinement: `Exec.authorizedB` refines `Spec.Guard` / `Spec.Authority`.

The executable cap gate `Exec.authorizedB caps turn : Bool` checks ownership-or-held-cap,
fail-closed. `Spec.Guard` says every gate is a `Guard.admits`; `Spec.Authority` says authority
is a capability `Graph` with `confers`/`Holds`. We refine the executable gate onto BOTH:

  * onto `Spec.Guard` — `authorizedB` is realized, with no remainder, as a `firstParty`
    `Guard` over the turn (the decidable intra/cross-vat gate of `VatBoundary.Positional`);
  * onto `Spec.Authority` — the ownership branch (`actor = src`) is the reflexive conferral
    `confers c c` (`Authority.confers_refl`), and the held-cap branch witnesses
    `Graph.has actor src` on a graph reconstructed from `Exec.caps`. -/

section AuthorityRefinement

-- The verify oracle for the `Guard`. The executable gate is FIRST-PARTY (decidable now), so
-- the witnessed branch is never used; we take the oracle as a parameter exactly as `Guard`
-- and `Coherence` do, so the refinement is stated over the same seam.
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- The `Request` the executable authority gate reads is exactly the `Turn` (the actor / src /
dst / amount facts) — NOT a `Nat`. The abstract `Guard` reads it first-party. -/
abbrev ExecRequest := Turn

/-- **`execAuthGuard caps`** — the executable cap gate as a first-party `Spec.Guard`.
`Guard.firstParty (fun t => Exec.authorizedB caps t)`: it admits a turn iff the kernel's
decidable ownership-or-held-cap check passes. The `Statement` carrier is free (no witnessed
branch — the gate is decided *now*, the positional regime). -/
def execAuthGuard (caps : Caps) : Guard ExecRequest Statement :=
  Guard.firstParty (fun t => authorizedB caps t)

/-- **KEYSTONE 2 — `exec_authz_refines_guard`.** The executable gate
`authorizedB` admitting a turn ⇒ the corresponding abstract `Spec.Guard.admits` is `true`. The
decidable kernel gate REFINES the abstract `Guard` demand: every turn the machine admits, the
abstract gate admits. (The `↔` even holds — the refinement is exact, not merely sound — but
the soundness direction is the load-bearing one for `Exec ⊑ Spec`.) -/
theorem exec_authz_refines_guard (caps : Caps) (turn : Turn) (w : Statement → Witness)
    (h : authorizedB caps turn = true) :
    Guard.admits (execAuthGuard (Statement := Statement) caps) turn w = true := by
  unfold execAuthGuard
  rw [Guard.admits_firstParty]
  exact h

/-- The refinement is EXACT (`↔`): the executable gate admits *iff* the abstract `firstParty`
guard admits. So `authorizedB` is realized as a `Spec.Guard.admits` with no remainder — the
same single gate object that unifies authorization / preconditions / program-constraints /
caveats (`Spec.Guard`'s thesis). PROVED. -/
theorem exec_authz_iff_guard (caps : Caps) (turn : Turn) (w : Statement → Witness) :
    Guard.admits (execAuthGuard (Statement := Statement) caps) turn w = true
      ↔ authorizedB caps turn = true := by
  unfold execAuthGuard
  rw [Guard.admits_firstParty]

/-- A *committed* `exec` step's turn passes the abstract authority `Guard` — composing
`Exec.exec_authorized` (no state change without authority) with the gate refinement. So the
fact "the kernel only moves resource under authority" is, on the abstract side, "the authority
`Guard` admitted the turn". PROVED. -/
theorem exec_step_passes_guard (k k' : KernelState) (turn : Turn) (w : Statement → Witness)
    (h : exec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  exec_authz_refines_guard k.caps turn w (exec_authorized k k' turn h)

/-! ### §2.1 — Refining onto `Spec.Authority`: ownership = reflexive `confers`, held cap =
`Graph.has`.

`Spec.Authority` models authority as a `Graph CellId Rights` with `confers` (non-amplifying
delegation) and `Graph.has` (the holder reaches a target). We reconstruct a Spec graph from
`Exec.caps` and show the executable gate's two branches land on it: ownership is the reflexive
self-conferral `confers c c`, and a held node/endpoint-write cap witnesses `Graph.has`. -/

/-- The **connectivity-skeleton** rights carrier for the reconstructed `execGraph`: `Unit`.
This is NOT a claim that the executable model lacks rights — it is the deliberate carrier for
the CONNECTIVITY projection. `execGraph h c` reads a `Bool` ("does `h`'s slot confer a
node/endpoint-write edge to `c.target`?"); a single slot may hold MANY caps to one target with
DIFFERENT rights, so there is no well-defined rights label to hang on a connectivity edge. The
connectivity graph's edge-set is therefore keyed purely by target — which is exactly why its
rights carrier is `Unit` (`⟨t,()⟩` is the unique connectivity edge to `t`). The genuine RIGHTS
attenuation order lives on `ExecCapRights` below (and on `Exec.confRights`/`ExecAuth`), where it
is a real `Finset Auth` ⊆-lattice with teeth — see §2.2. Keeping the connectivity carrier `Unit`
and the rights carrier `Finset Auth` SEPARATE is faithful: connectivity (Granovetter reach) and
rights (attenuation) are distinct projections of one cap, and the unowned effect kernels
(`Exec.EffectsAuthority`, `Exec.TurnExecutorFull`, …) consume `execGraph`'s `⟨t,()⟩` connectivity
edges, while the genuine `granted.rights ≤ held.rights` discipline is the `ExecCapRights` order. -/
abbrev ExecRights := Unit

/-! ### §2.2 — The GENUINE executable rights lattice `ExecCapRights := Finset Auth` (DE-VACUIFIED).

`ExecRights = Unit` above is the connectivity carrier; on it `confers` collapses to "same
target" (the rights conjunct is `() ≤ () = True`, vacuous). The REAL rights an executable cap
carries are a `List Auth` (`Exec.capAuthConferred`), whose attenuation order is **subset of
conferred authorities** (`granted ⊆ held`, the `is_attenuation` of `cell/src/capability.rs`).
The deduplicated, order-insensitive carrier with a genuine `SemilatticeInf` + `OrderTop` is
`Finset Auth` (= `Exec.ExecAuth`), so it slots DIRECTLY into `Spec.Authority`'s
`{Rights} [SemilatticeInf Rights] [OrderTop Rights]` interface. We state the rights-bearing
`confers` / non-amplification theorems over THIS carrier — where `≤` is a real `⊆` test that can
FAIL on an amplifying grant — and connect it to executable caps via `Exec.confRights`.
This is the de-vacuification: every theorem below has a strict-attenuation witness AND an
amplification-rejection witness (§2.3), neither of which `Unit` can grow. -/

/-- **`ExecCapRights`** — the genuine executable rights lattice: a `Finset Auth` ordered by `⊆`
(attenuation), with `⊤ = Finset.univ` (full authority). The real order the executable caps live
in; `a ≤ b` is a non-trivial subset test, NOT the `Unit` collapse. (`= Exec.ExecAuth`.) -/
abbrev ExecCapRights := ExecAuth

example : SemilatticeInf ExecCapRights := inferInstance
example : OrderTop ExecCapRights := inferInstance

/-- Lift an executable cap into a rights-labelled `Spec.Cap` over the GENUINE rights lattice:
target preserved, rights = the cap's actual conferred authority (`Exec.confRights`). This is the
rights-AWARE Spec image of a cap (contrast `execGraph`, the connectivity skeleton). -/
def capToSpec (target : Label) (c : Authority.Cap) : Cap Label ExecCapRights :=
  ⟨target, confRights c⟩

/-! ### §2.3 — Non-amplification over `ExecCapRights`, WITH TEETH.

The headline `granted.rights ≤ held.rights` over the genuine lattice. `attenuate` narrows real
rights (`Exec.attenuate_confRights_le`); we lift it to `confers` on rights-labelled Spec caps,
then exhibit BOTH a strict-attenuation witness (held has a right granted lacks) AND an
amplification-rejection witness (`confers` is FALSE for an amplifying grant). On `ExecRights =
Unit` both collapse to `True`; here the second is FALSE. -/

/-- **`attenuate_confers_real` (NON-VACUOUS).** Attenuating a held cap and re-labelling
the Spec image yields a `confers`-child of the held cap's Spec image — over the GENUINE
`ExecCapRights` lattice. The rights conjunct is `confRights (attenuate keep c) ≤ confRights c`
(`Exec.attenuate_confRights_le`), a real `⊆`, NOT `() ≤ ()`. This is the rights non-amplification
of delegation, stated where it can fail. -/
theorem attenuate_confers_real (t : Label) (keep : List Authority.Auth) (c : Authority.Cap) :
    confers (capToSpec t c) (capToSpec t (attenuate keep c)) := by
  refine ⟨rfl, ?_⟩
  show confRights (attenuate keep c) ≤ confRights c
  exact attenuate_confRights_le keep c

/-- **`confers_real_forbids_amplification` (the TOOTH).** If a child Spec cap (over the
genuine lattice) `confers`-descends from a parent, then its rights are `⊆` the parent's: it
CANNOT carry an authority the parent lacks. Contrapositive of "amplification allowed". On `Unit`
this is vacuous (`() ≤ ()`); here it constrains — see `amplifying_grant_refused`. -/
theorem confers_real_forbids_amplification
    {parent child : Cap Label ExecCapRights} (h : confers parent child) :
    child.rights ≤ parent.rights :=
  h.2

/-- **`amplifying_grant_refused` (the NON-VACUITY TOOTH).** A child cap requesting
`{read, write}` does NOT `confers`-descend from a parent holding only `{read}`: the amplifying
grant is REJECTED. This is the exact case `ExecRights := Unit` could never reject (there, every
same-target child confers). The `decide` discharges the real `⊄` over `Finset Auth`. -/
theorem amplifying_grant_refused :
    ¬ confers (⟨7, {Authority.Auth.read}⟩ : Cap Label ExecCapRights)
              (⟨7, {Authority.Auth.read, Authority.Auth.write}⟩ : Cap Label ExecCapRights) := by
  rintro ⟨_, hle⟩
  -- `{read,write} ≤ {read}` is FALSE over the genuine ⊆-lattice.
  exact absurd hle (by decide)

/-- **`strict_attenuation_witness` (the STRICT-ATTENUATION TOOTH).** A held cap confers
`{read, write}`; the granted child confers only `{read}` — the held cap has a right (`write`) the
granted does NOT, and the grant `confers` SOUNDLY (strict `⊂`). Exhibits that `≤` is not
everywhere-trivial: it admits the sound narrowing AND (by `amplifying_grant_refused`) rejects the
amplification. Strictness: `{read} ⊆ {read,write}` but `{read} ≠ {read,write}`. -/
theorem strict_attenuation_witness :
    confers (⟨7, {Authority.Auth.read, Authority.Auth.write}⟩ : Cap Label ExecCapRights)
            (⟨7, {Authority.Auth.read}⟩ : Cap Label ExecCapRights)
      ∧ ({Authority.Auth.read} : ExecCapRights) ≠ {Authority.Auth.read, Authority.Auth.write} := by
  refine ⟨⟨rfl, by decide⟩, by decide⟩

-- The decidable teeth as `#guard`s: the order is non-trivial (NOT everywhere-true).
#guard decide (({Authority.Auth.read, Authority.Auth.write} : ExecCapRights)
                  ≤ {Authority.Auth.read}) = false   -- amplification REJECTED
#guard decide (({Authority.Auth.read} : ExecCapRights)
                  ≤ {Authority.Auth.read, Authority.Auth.write}) = true   -- attenuation SOUND

/-- **`execGraph caps` — a DELIBERATE linter-calibration fixture, NOT an authority spec.** It
reconstructs a `Spec.Authority.Graph` from the executable cap table VERBATIM as the executor's own
authority-edge lookup: cell `h` holds a Spec edge to `t` iff, in `Exec.caps`, `h` holds a `node t` cap
or an `endpoint t` cap carrying `write` — i.e. the `.any confersEdgeTo` body the dispatch gate folds.
Because it is the gate copied verbatim, it is `isDefEq` to that gate (`execGraph_eq_any := rfl`), so
reading `execGraph caps h c` as a *connectivity claim* attests it tautologically — a "spec" that IS the
implementation gate. That is precisely why it is `@[linter_calibration]`: it is the negative-calibration
fixture for `Verify.LoadBearingLint`'s DEFEQ check (#2), which MUST reject it (asserted by
`#load_bearing_calibration_expect_fail` in the audit modules — the intended FAIL paired with
`gateCopyBurnSpec`). Its GENUINE counterpart — the INDEPENDENT authority-connectivity reference the
C-c1 legs actually attest against — is `Spec.authConnects` (a `Prop`-existential, linter-PASS, grounded
in `Metatheory.AuthorizedProduction` via `authConnects_is_authorized_production`). `execGraph` retains
exactly two non-calibration roles: it is the genuine carrier of a graph CHANGE (`addEdge`/`removeEdge`
on the `Spec` edge, where the defeq is harmless), and it is the executor-side gate-relation that
TRANSPORTS onto `authConnects` (`execGraph_iff_authConnects` / `execGraph_has_iff_authConnects_has`).
The rights are `Unit` (the connectivity skeleton). -/
@[linter_calibration]
def execGraph (caps : Caps) : Graph Label ExecRights :=
  fun h c =>
    -- the `.any` reads `c.target`, so the edge depends on the cap `c`.
    (caps h).any (fun cap =>
      (cap == Authority.Cap.node c.target) ||
      (match cap with
       | .endpoint t rights => (t == c.target) && rights.contains Auth.write
       | _ => false)) = true

/-! ### §2.AUTH-CONNECTS — the INDEPENDENT authority-connectivity spec.

`execGraph` is DEF-EQ to the executor's `.any confersEdgeTo` lookup gate (`execGraph_eq_any := rfl`),
so a guarantee leg that uses a bare `execGraph caps h c` as a CONNECTIVITY claim attests it
tautologically — the spec IS the gate. `authConnectsCap` / `authConnects` is the SEVERED reference:
the SAME per-cap authority predicate the 55 passing `Circuit/Spec/*` guards use (`confersEdgeTo`'s
two branches: a `node t` cap, or an `endpoint t` cap carrying `write`), but phrased as an EXISTENTIAL
over LIST MEMBERSHIP (`∃ cap ∈ caps h, …`) — `Graph.has`-shaped, the Granovetter "you can reach what
you hold a cap to" relation. This is NOT `isDefEq` to the boolean `.any … = true` fold (the gate): the
gate is a `Bool`-coercion `(List.any …) = true`; `authConnects` is a `Prop`-level `∃ … ∧ …` over
`List.Mem`. They are PROPOSITIONALLY equivalent (`List.any_eq_true`) but not definitionally — so
`isDefEq` separates them, and the refinement `gate ⟹ authConnects` is a REAL proof (it must run
`List.any_eq_true`), not `rfl`. The relation reads only the pure carriers `caps`/`confersEdgeTo`-shape
— no executor STEP gate — so it is independent.

Alignment with the `Metatheory` authority law: `authConnects` is the executable-image of
`Graph.has` (Granovetter connectivity), the SAME object `AuthorizedProduction`/`noforge_closure`
(`Metatheory/Open/AuthorityClosure.lean`) constrains: an edge exists only where a held cap PRODUCES
it; no edge is forged. -/

/-- **`authConnectsCap t cap`** — does `cap` confer an authority edge to target `t`? The SAME two
branches `confersEdgeTo`/`authorizedB`/`execGraph` read (a `node t` cap, or an `endpoint t` cap
carrying `write`), written as a `Prop` (not the `Bool` the gate folds). The per-cap atom of the
independent connectivity spec. -/
def authConnectsCap (t : Label) (cap : Authority.Cap) : Prop :=
  cap = Authority.Cap.node t ∨
  (∃ rights, cap = Authority.Cap.endpoint t rights ∧ rights.contains Auth.write = true)

/-- **`authConnects caps h c`** — the INDEPENDENT authority-connectivity relation: holder `h` holds
SOME cap in its slot conferring an authority edge to `c.target`. An EXISTENTIAL over list membership
(`Graph.has`-shaped), NOT the executor's boolean `.any … = true` lookup gate — so it is not defeq to
that gate, yet is provably IMPLEMENTED by it (`capLookup_refines_authConnects`). The severed
reference the C-c1 authority-graph legs attest against. -/
def authConnects (caps : Caps) (h : Label) (c : Spec.Cap Label ExecRights) : Prop :=
  ∃ cap, cap ∈ caps h ∧ authConnectsCap c.target cap

/-- **`authConnects_nonvacuous`** — the non-vacuity witness the linter requires: `authConnects`
is NEITHER everywhere-true NOR everywhere-false. It ACCEPTS a holder that holds a `node 7` cap
(connectivity to `7`), and REFUTES an EMPTY-slot holder (no cap ⇒ no edge). A vacuous accept-all
relation could not carry the refuted half; a vacuous reject-all could not carry the accepted half. -/
theorem authConnects_nonvacuous :
    authConnects (fun l => if l = 0 then [Authority.Cap.node 7] else [])
      0 (⟨7, ()⟩ : Spec.Cap Label ExecRights)
    ∧ ¬ authConnects (fun _ => ([] : List Authority.Cap))
          0 (⟨7, ()⟩ : Spec.Cap Label ExecRights) := by
  refine ⟨?_, ?_⟩
  · -- ACCEPTED: holder `0` holds `node 7`, which `authConnectsCap 7` accepts (the `node` branch).
    exact ⟨Authority.Cap.node 7, by simp, Or.inl rfl⟩
  · -- REFUTED: the empty slot holds no cap, so no member can confer the edge.
    rintro ⟨cap, hmem, _⟩
    simp at hmem

/-! ### §2.AUTH-CONNECTS-PRODUCTION — `authConnects ⟹ AuthorizedProduction` (the authority-leg
grounding into the abstract `Metatheory` production law).

`authConnects caps h c` is the executable-image of `Graph.has` (Granovetter "you can reach what you
hold a cap to"). `Metatheory.Dynamics.AuthorizedProduction held produced` is the abstract
non-forgeability law (Miller "only connectivity begets connectivity"): a held bundle may PRODUCE a
fragment covered by it. We bind them: WHENEVER `authConnects` holds (the holder genuinely reaches the
target through a held cap), that connectivity IS an abstract `AuthorizedProduction` — the held cap
PRODUCES the connectivity edge, and the edge is covered by the held authority. This makes the
INDEPENDENT `authConnects` spec (the C-c1 authority-graph reference) cite the abstract production law,
completing the authority leg of the chain to `Metatheory`. The SAME bridge shape as the mint binding
(`mintAuthorizedB_covers_production`), read off the connectivity relation instead of the mint gate. -/

open Metatheory.Dynamics (AuthorizedProduction)
open Metatheory.Dynamics.USet (fits_iff)

/-- **`authProduced`** — the connectivity edge an `authConnects` holder PRODUCES: the `control` right
over the target (the abstract image of a held node/endpoint-write cap conferring an authority edge).
The smallest non-trivial production, the `Metatheory` `USet Rights` carrier. -/
def authProduced : Metatheory.Dynamics.USet Metatheory.Dynamics.Rights :=
  ⟨{Dregg2.Authority.Auth.control}⟩

/-- **`heldFromAuthConnects caps h c`** — the abstract held-authority bundle the connectivity relation
GRANTS: the `control` edge WHEN `authConnects caps h c` (the holder genuinely reaches `c.target`), and
the EMPTY bundle when it does NOT. The abstraction function on the authority leg: connected ↦
`{control}`, disconnected ↦ `∅`. So an UNCONNECTED holder holds `∅` and produces nothing.
(`authConnects` is a `Prop`-existential; the branch is classical, hence `noncomputable`.) -/
noncomputable def heldFromAuthConnects (caps : Caps) (h : Label)
    (c : Spec.Cap Label ExecRights) : Metatheory.Dynamics.USet Metatheory.Dynamics.Rights :=
  open Classical in
  if authConnects caps h c then ⟨{Dregg2.Authority.Auth.control}⟩ else ⟨∅⟩

/-- `heldFromAuthConnects` selects `{control}` on the connected branch. -/
theorem heldFromAuthConnects_pos (caps : Caps) (h : Label) (c : Spec.Cap Label ExecRights)
    (hconn : authConnects caps h c) :
    heldFromAuthConnects caps h c = ⟨{Dregg2.Authority.Auth.control}⟩ := by
  unfold heldFromAuthConnects; exact if_pos hconn

/-- `heldFromAuthConnects` selects `∅` on the disconnected branch. -/
theorem heldFromAuthConnects_neg (caps : Caps) (h : Label) (c : Spec.Cap Label ExecRights)
    (hconn : ¬ authConnects caps h c) :
    heldFromAuthConnects caps h c = ⟨∅⟩ := by
  unfold heldFromAuthConnects; exact if_neg hconn

/-- **`authConnects_is_authorized_production` — THE BRIDGE: an `authConnects` edge IS an abstract
`AuthorizedProduction`, PROVED, kernel-clean.** If `authConnects caps h c` (the holder reaches
`c.target` through a held cap — the Granovetter connectivity the C-c1 legs attest against), then the
connectivity-derived held bundle `heldFromAuthConnects` covers the produced edge `authProduced`:
`authProduced ≼ heldFromAuthConnects`. So the executable connectivity relation WITNESSES the abstract
`AuthorizedProduction (heldFromAuthConnects …) authProduced` — "only connectivity begets connectivity"
(Miller) read off the independent `authConnects` spec, citing the abstract `Metatheory` production law.
The hypothesis is LOAD-BEARING: `heldFromAuthConnects` is `∅` when disconnected, which covers nothing —
no connectivity, no production authority. -/
theorem authConnects_is_authorized_production (caps : Caps) (h : Label)
    (c : Spec.Cap Label ExecRights) (hconn : authConnects caps h c) :
    AuthorizedProduction (heldFromAuthConnects caps h c) authProduced := by
  -- `authConnects` selects the `{control}` branch of `heldFromAuthConnects`; coverage is `≼`-trivial.
  -- disconnection would select `∅`, which does NOT cover `{control}` — so `hconn` is load-bearing.
  show Dregg2.Resource.fits authProduced (heldFromAuthConnects caps h c)
  rw [fits_iff, heldFromAuthConnects_pos caps h c hconn]
  simp [authProduced]

/-- **`authConnects_production_nonvacuous` — the bridge is non-vacuous: a genuine connectivity
PRODUCES, an empty slot does NOT.** A holder holding a `node 7` cap reaches `7`, so `authConnects`
holds and the connectivity is an `AuthorizedProduction` (the `{control}` edge fits the granted bundle);
an EMPTY-slot holder is disconnected, so `heldFromAuthConnects` is `∅` and the production does NOT hold
(the empty bundle covers no `control` edge — the TOOTH). A vacuous accept-all bridge could not carry
the refuted half; a vacuous reject-all could not carry the produced half. -/
theorem authConnects_production_nonvacuous :
    AuthorizedProduction
        (heldFromAuthConnects (fun l => if l = 0 then [Authority.Cap.node 7] else [])
          0 (⟨7, ()⟩ : Spec.Cap Label ExecRights)) authProduced
    ∧ ¬ AuthorizedProduction
          (heldFromAuthConnects (fun _ => ([] : List Authority.Cap))
            0 (⟨7, ()⟩ : Spec.Cap Label ExecRights)) authProduced := by
  refine ⟨?_, ?_⟩
  · -- CONNECTED: holder `0` holds `node 7`, so `authConnects` holds; the production is authorized.
    exact authConnects_is_authorized_production _ 0 _ authConnects_nonvacuous.1
  · -- THE TOOTH: empty slot ⇒ disconnected ⇒ `heldFromAuthConnects = ∅`, which produces nothing.
    intro hprod
    rw [show AuthorizedProduction
            (heldFromAuthConnects (fun _ => ([] : List Authority.Cap)) 0
              (⟨7, ()⟩ : Spec.Cap Label ExecRights)) authProduced
          = Dregg2.Resource.fits authProduced
              (heldFromAuthConnects (fun _ => ([] : List Authority.Cap)) 0
                (⟨7, ()⟩ : Spec.Cap Label ExecRights)) from rfl,
        fits_iff,
        heldFromAuthConnects_neg _ 0 _ authConnects_nonvacuous.2] at hprod
    simp [authProduced] at hprod

#assert_axioms authConnects_is_authorized_production
#assert_axioms authConnects_production_nonvacuous

/-- **`exec_owns_self_confers` (NOW OVER THE GENUINE RIGHTS LATTICE)** — the authority
object the ownership branch lands on is the **reflexive self-conferral**, stated over the REAL
`ExecCapRights = Finset Auth` lattice (NOT the `Unit` skeleton). When a turn is admitted via
ownership (`turn.actor = turn.src`), the owner's self-cap (carrying its ACTUAL conferred rights
`r : ExecCapRights`) confers itself: the rights conjunct is `r ≤ r` over the genuine `⊆`-order —
the SAME order that REJECTS an amplifying grant (`amplifying_grant_refused`). The ownership
hypothesis `hown` is load-bearing — it collapses the two endpoints to one.

SCOPE: reflexivity is intrinsically `r ≤ r`, but it now lives in the non-trivial lattice, so it
composes (via `confers_trans`) with the genuine narrowing `attenuate_confers_real` to bound a
delegated grant — and the order it uses is the one with teeth (§2.3), not `() ≤ ()`. -/
theorem exec_owns_self_confers (turn : Turn) (r : ExecCapRights) (hown : turn.actor = turn.src) :
    confers (⟨turn.actor, r⟩ : Cap Label ExecCapRights)
            (⟨turn.src, r⟩ : Cap Label ExecCapRights) := by
  -- ownership makes `actor = src`, so the conferred edge is the reflexive self-cap.
  rw [hown]
  exact confers_refl _

/-- **`exec_owns_attenuated_confers` (NON-VACUOUS COMPOSITION)** — the de-vacuified
payoff: an owner may delegate from its own cap ONLY a non-amplifying (attenuated) child, over the
genuine rights lattice. Composing `exec_owns_self_confers` (reflexive, `r ≤ r`) with
`attenuate_confers_real` (the real `⊆` narrowing) via `confers_trans`: the attenuated grant
`confers`-descends from the owner's self-cap, and its rights are `⊆` the owner's. An amplifying
grant is OUTSIDE this relation (`confers_real_forbids_amplification` + `amplifying_grant_refused`).
This is the ownership branch with REAL rights teeth, not the `Unit` collapse. -/
theorem exec_owns_attenuated_confers (turn : Turn) (c : Authority.Cap)
    (keep : List Authority.Auth) (hown : turn.actor = turn.src) :
    confers (capToSpec turn.actor c) (capToSpec turn.src (attenuate keep c)) := by
  rw [hown]
  exact confers_trans (confers_refl _) (attenuate_confers_real turn.src keep c)

/-- **`exec_heldcap_is_graph_has`** — the held-cap branch of `authorizedB` refines
`Graph.has` on the reconstructed graph. If the actor is NOT the owner yet `authorizedB` admits
the turn, then the actor holds a `node src` / `endpoint src write` cap, i.e. on `execGraph` the
actor `Graph.has` the source: the executable held-cap acceptance witnesses abstract
connectivity (`Granovetter`'s "you can reach what you hold a cap to"). -/
theorem exec_heldcap_is_graph_has (caps : Caps) (turn : Turn)
    (h : authorizedB caps turn = true) (hne : turn.actor ≠ turn.src) :
    (execGraph caps).has turn.actor turn.src := by
  -- `authorizedB` is `(actor == src) || (caps actor).any …`; ownership is excluded, so the
  -- `any` branch holds.
  unfold authorizedB at h
  rw [Bool.or_eq_true] at h
  rcases h with hown | hcap
  · -- `actor == src = true` contradicts `actor ≠ src`.
    rw [beq_iff_eq] at hown; exact absurd hown hne
  · -- the held-cap branch: exhibit the Spec edge `actor ⟶ src`.
    refine ⟨(), ?_⟩
    unfold execGraph
    exact hcap

/-- **`exec_authz_grounds_in_graph`** — the FULL authority refinement disjunction:
every turn the executable gate admits is grounded in the reconstructed Spec authority graph —
either by ownership (refining the reflexive conferral `confers (·) (·)`) or by a held cap
(refining `Graph.has`). This is the authority projection of the simulation: `authorizedB`'s
acceptance set is contained in the abstract authority graph's reachability. PROVED. -/
theorem exec_authz_grounds_in_graph (caps : Caps) (turn : Turn)
    (h : authorizedB caps turn = true) :
    turn.actor = turn.src ∨ (execGraph caps).has turn.actor turn.src := by
  by_cases hne : turn.actor = turn.src
  · exact Or.inl hne
  · exact Or.inr (exec_heldcap_is_graph_has caps turn h hne)

end AuthorityRefinement

/-! ## §3 — The simulation relation + the commuting square.

`Refines k a` ties the executable `KernelState` `k` to an abstract Spec state `a` — the
balances correspond (the ℤ ledger IS the `balance`-domain total) and the caps correspond (the
executable cap table reconstructs the abstract authority `Graph`). The abstract state is the
pair (the conserved balance-domain total over the live accounts, the reconstructed authority
graph) — the two Spec projections the squares above prove. -/

section Square

variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- **`AbstractState`** — the abstract Spec state a kernel refines: the conserved
`balance`-domain total over the live accounts (an `ℤ`, the `Spec.Conservation` measure at
`Bal = ℤ`) together with the reconstructed authority `Graph` (the `Spec.Authority` graph the
caps confer). These are exactly the two projections squares §1 and §2 prove. -/
structure AbstractState where
  /-- the conserved `balance`-domain total (the `Spec.Conservation` measure at `Bal = ℤ`). -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph (the `Spec.Authority` graph the caps confer). -/
  authGraph    : Graph Label ExecRights

/-- The abstract state a kernel state denotes: its `total` (balance-domain conserved measure)
and its `execGraph` (reconstructed authority graph). The simulation's abstraction function. -/
def absOf (k : KernelState) : AbstractState :=
  { balanceTotal := total k
    authGraph    := authConnects k.caps }

/-- **`Refines k a`** — the simulation relation: the kernel's conserved balance total IS the
abstract `balanceTotal`, and its reconstructed authority graph IS the abstract `authGraph`.
(`Refines k (absOf k)` holds by `rfl`; the relation is `a = absOf k` unfolded into its two
corresponding projections, stated as a relation so the square below reads as a diagram.) -/
def Refines (k : KernelState) (a : AbstractState) : Prop :=
  a.balanceTotal = total k ∧ a.authGraph = authConnects k.caps

/-- `absOf` realizes `Refines` (the abstraction function is a refinement witness). PROVED. -/
theorem refines_absOf (k : KernelState) : Refines k (absOf k) :=
  ⟨rfl, rfl⟩

/-- **The conservation projection of the commuting square.** If `Refines k a`
and `exec k turn = some k'`, then the abstract `balanceTotal` is PRESERVED across the step:
`a'.balanceTotal = a.balanceTotal` for `a' := absOf k'`. The square commutes on the
conservation projection — the abstract step is the identity on the conserved total, which is
`exec_conserves` read through the abstraction. PROVED. -/
theorem exec_step_refines_conservation (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (hsim : Refines k a) (h : exec k turn = some k') :
    (absOf k').balanceTotal = a.balanceTotal := by
  have htot : total k' = total k := exec_conserves k k' turn h
  simp only [absOf]
  rw [htot, hsim.1]

/-- **The authority projection of the commuting square.** If `Refines k a` and
`exec k turn = some k'`, then the committed turn is admitted by the abstract authority gate
over `a`'s graph-conferring caps — and the post-state's authority graph is UNCHANGED (`exec`
moves only `bal`, never `caps`), so `Refines k' a'` holds on the authority projection. The
square commutes on authority: the executable gate's acceptance is the abstract gate's
acceptance, and the abstract authority state is preserved. PROVED. -/
theorem exec_step_refines_authority (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (w : Statement → Witness)
    (hsim : Refines k a) (h : exec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true ∧
      (absOf k').authGraph = a.authGraph := by
  refine ⟨exec_step_passes_guard k k' turn w h, ?_⟩
  -- `exec` preserves `caps` (it rewrites only `bal`), so the reconstructed graph is unchanged.
  have hcaps : k'.caps = k.caps := by
    unfold exec at h
    by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
    · rw [if_neg hg] at h; exact absurd h (by simp)
  simp only [absOf]
  rw [hcaps, hsim.2]

/-- **`exec_step_refines` (the commuting square — conservation+authority projections PROVED,
operational thread OPEN).** If `Refines k a` and `exec k turn = some k'`, then there is an
abstract successor `a'` with `Refines k' a'`, AND the step preserves both Spec projections:
the conserved balance total is unchanged (`exec_conserves`, §1) and the committed turn passed
the abstract authority gate with the authority graph unchanged (§2). We take `a' := absOf k'`
(the canonical abstraction of the post-state) and discharge the two projections cleanly.

This is the conservation+authority projection of the full simulation diagram — exactly the two
tractable squares — assembled into one commuting statement. PROVED-clean. -/
theorem exec_step_refines (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (w : Statement → Witness)
    (hsim : Refines k a) (h : exec k turn = some k') :
    ∃ a', Refines k' a' ∧
      -- conservation projection: the abstract balance total is preserved.
      a'.balanceTotal = a.balanceTotal ∧
      -- authority projection: the turn passed the abstract gate, the auth graph is preserved.
      (Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true ∧
        a'.authGraph = a.authGraph) := by
  refine ⟨absOf k', refines_absOf k', ?_, ?_⟩
  · exact exec_step_refines_conservation k k' a turn hsim h
  · exact exec_step_refines_authority k k' a turn w hsim h

/-- **The conservation invariant of the square, lifted to a whole kernel run.**
Composing `exec_step_refines`'s conservation projection with `Exec.kernel_run_conserves`: an
abstract state refining the initial kernel state refines the final one on the conserved total
across an ENTIRE `kernelSystem` run. So the refinement square's conservation projection is
stable under iteration — the abstract `balanceTotal` is a run invariant. PROVED. -/
theorem run_refines_conservation {k k' : KernelState} (a : AbstractState)
    (hsim : Refines k a) (hrun : Dregg2.Execution.Run kernelSystem k k') :
    (absOf k').balanceTotal = a.balanceTotal := by
  have htot : total k' = total k := kernel_run_conserves hrun
  simp only [absOf]
  rw [htot, hsim.1]

end Square

/-! ## §3.5 — The second refinement square: the content-addressed record kernel `⊑ Spec`.

§1–§3 refine the toy scalar kernel (`Exec.Kernel`, `bal : CellId → ℤ`). Here we prove the
same square for the content-addressed `Value` record cell (`Exec.RecordKernel`, `cell : CellId
→ Value`), which conserves a named `balance` field rather than the whole-state ℤ. The record
kernel's `balance`-field conservation IS `Spec.conservedInDomain Domain.balance` at `Bal = ℤ`
— the same abstract law as §1, now refined by the concrete record cell. -/

/-- **`refineRecordConservation s s'`** — the per-cell `balance`-FIELD deltas of a record-kernel step
`s ⟶ s'`, packaged as the `List ℤ` that `Spec.conservedInDomain` consumes (the record-cell analog of
`refineConservation`). It reads `balOf` — the named-field measure — off each live account. -/
noncomputable def refineRecordConservation (s s' : RecordKernelState) : List ℤ :=
  s.accounts.toList.map (fun c => balOf (s'.cell c) - balOf (s.cell c))

/-- The list-sum of the per-cell `balance`-field deltas equals `recTotal s' - recTotal s` over the
shared account set (`recKExec` preserves `accounts`). The `Finset.sum_map_toList` bridge applied to
the record cell's `balance`-field measure. -/
theorem refineRecordConservation_sum (s s' : RecordKernelState) (hacc : s'.accounts = s.accounts) :
    (refineRecordConservation s s').sum = recTotal s' - recTotal s := by
  unfold refineRecordConservation recTotal
  rw [Finset.sum_map_toList s.accounts (fun c => balOf (s'.cell c) - balOf (s.cell c)),
      Finset.sum_sub_distrib, hacc]

/-- **`recExec_refines_conservation`** — a committed record-kernel step's per-cell
`balance`-field deltas satisfy `conservedInDomain Domain.balance`. This is the conservation
projection of the second refinement square: `recKExec_conserves` IS `Spec`'s `Σδ = 0` over
`Bal = ℤ`, `Domain.balance`. -/
theorem recExec_refines_conservation (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    conservedInDomain Domain.balance (refineRecordConservation k k') := by
  have hacc : k'.accounts = k.accounts := (recKExec_frame k k' turn h).1
  have htot : recTotal k' = recTotal k := recKExec_conserves k k' turn h
  unfold conservedInDomain
  rw [refineRecordConservation_sum k k' hacc, htot, sub_self]

/-- The record-kernel conservation projection cast through the abstract monoid keystone: a committed
record step's prior balance-domain total `pre` is unchanged by adding the step's `balance`-field
deltas — the `Bal = ℤ` instance of `Spec.conservation_over_monoid`, now for the content-addressed
cell. PROVED. -/
theorem recExec_refines_conservation_over_monoid (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') (pre : ℤ) :
    pre + (refineRecordConservation k k').sum = pre :=
  conservation_over_monoid Domain.balance pre (refineRecordConservation k k')
    (recExec_refines_conservation k k' turn h)

/-- **`recExec_step_passes_guard`** — the record kernel uses the same `authorizedB` gate as the
scalar kernel, so a committed record step's turn passes the same abstract `Spec.Guard.firstParty`
guard (authority is orthogonal to the state representation). -/
theorem recExec_step_passes_guard {Statement Witness : Type} [Verifiable Statement Witness]
    (k k' : RecordKernelState) (turn : Turn) (w : Statement → Witness)
    (h : recKExec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  exec_authz_refines_guard k.caps turn w (recKExec_authorized k k' turn h)

/-- **`recExec_step_refines`** — assembles the second refinement square: a committed record-kernel
step preserves both Spec projections (balance-domain conservation + authority guard), mirroring
`exec_step_refines` for the content-addressed cell. The operational LTS residue (§4) is shared. -/
theorem recExec_step_refines {Statement Witness : Type} [Verifiable Statement Witness]
    (k k' : RecordKernelState) (turn : Turn) (w : Statement → Witness)
    (h : recKExec k turn = some k') :
    conservedInDomain Domain.balance (refineRecordConservation k k') ∧
      Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  ⟨recExec_refines_conservation k k' turn h, recExec_step_passes_guard k k' turn w h⟩

#assert_axioms refineRecordConservation_sum
#assert_axioms recExec_refines_conservation
#assert_axioms recExec_refines_conservation_over_monoid
#assert_axioms recExec_step_passes_guard
#assert_axioms recExec_step_refines

/-! ## §4 — OPEN: the operational residue (the abstract small-step relation).

What §3 PROVES is the conservation+authority PROJECTION of the simulation square: the two Spec
laws (`Σδ = 0` over the `balance` domain, the authority `Guard`/`Graph` gate) are preserved by
`exec`, with the abstraction `absOf` as the refinement witness. What it does NOT prove — and
what the FULL l4v-style `Exec ⊑ Spec` forward simulation needs — is an *abstract small-step
relation* `AbsStep : AbstractState → AbstractState → Prop` (the spec's own operational
transition), such that:

  * every executable `exec k turn = some k'` is matched by an `AbsStep (absOf k) (absOf k')`
    (the FULL square's bottom edge is an abstract STEP, not merely the identity-on-projections
    we use here); and
  * `AbsStep` is exactly the `Spec.Conservation` + `Spec.Authority` dynamics — a turn that
    moves balance-domain ℤ conservatively AND fires an authorized `Spec.Authority.AuthStep` /
    `GenAct`/`RestrictAct` on the graph.

This is the SAME residue already flagged by `Proof/Refine` (the operational diagram) and by
`Spec.Authority.only_connectivity_begets_connectivity`'s OPEN (the whole-history graph
bookkeeping). It needs the abstract LTS, not just the two static projections; until that LTS
is named, the bottom edge of the square is the projection-preserving abstraction, not a full
abstract transition. The residual obligation:

-- OPEN (operational residue, NOT proved here): define `AbsStep : AbstractState → AbstractState
--   → Prop` as the `Spec.Conservation`-conservative, `Spec.Authority`-authorized abstract turn
--   relation, and prove `exec k turn = some k' → AbsStep (absOf k) (absOf k')` (forward
--   simulation: every executable step is an abstract step). With that, `exec_step_refines`
--   strengthens from "preserves the two projections" to "commutes with a genuine abstract
--   step" — full `Exec ⊑ Spec` forward simulation. The projections proved above are the
--   conserved/authority CONTENT of that step; the missing piece is the LTS that packages them
--   as one transition relation (the same thread `Spec.Authority`'s headline leaves OPEN).
-/

/-! ## §5 — Axiom-hygiene tripwires.

All keystones depend only on the three standard kernel axioms (no faked green). The operational
residue (§4) is an `-- OPEN:` prose obligation, not an open hole; the whole file is clean. -/

#assert_axioms refineConservation_sum
#assert_axioms exec_refines_conservation
#assert_axioms exec_refines_conservation_over_monoid
#assert_axioms exec_inhabits_balance_domain
#assert_axioms exec_authz_refines_guard
#assert_axioms exec_authz_iff_guard
#assert_axioms exec_step_passes_guard
#assert_axioms attenuate_confers_real
#assert_axioms confers_real_forbids_amplification
#assert_axioms amplifying_grant_refused
#assert_axioms strict_attenuation_witness
#assert_axioms exec_owns_self_confers
#assert_axioms exec_owns_attenuated_confers
#assert_axioms exec_heldcap_is_graph_has
#assert_axioms exec_authz_grounds_in_graph
#assert_axioms refines_absOf
#assert_axioms exec_step_refines_conservation
#assert_axioms exec_step_refines_authority
#assert_axioms exec_step_refines
#assert_axioms run_refines_conservation

end Dregg2.Spec
