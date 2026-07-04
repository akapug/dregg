/-
# Dregg2.Firmament.CapGradation — the FORMAL LEAN SEMANTICS of the firmament cap-gradation.

`sel4/dregg-firmament/` is a runnable Rust crate (`docs/FIRMAMENT.md §3`,
`docs/DREGG-DESKTOP-OS.md §L2`): ONE `Capability { target, rights }` handle whose
`Target` is `Local { slot }` (an seL4 CNode slot), `Distributed { cell }` (a dregg
cell on a federation), or `Surface { cell }` (a dregg cell rendered as a window — the
firmament made visual). A `FirmamentRouter` dispatches an invocation by the handle's
`Target` alone; the app cannot tell which backing it holds, and **adoption is
attenuation** at all three ends — the same `granted ⊆ held` gate. The distance
parameter `n` slides the *bounds* (immediate↔eventual revocation, synchronous↔quorum
commit), never the verbs; at `n = 1` the distributed bounds collapse to strong-local.

That crate is the EXECUTABLE. This module is the **formal semantics it refines**
(law #1: the desktop substrate's semantics is proven from Lean, not just asserted in
Rust). It is the l4v data-refinement obligation: the Lean model `⊑` the Rust impl —
each theorem below is the refinement obligation FOR a named Rust function, noted at the
theorem.

## We REUSE the existing dregg cap metatheory — we do NOT reinvent it (the WELD method)

The firmament rides the EXISTING attenuation lattice. We import:

  * `Dregg2.Exec.CapTPConcrete.AuthReq` — the concrete `AuthRequired` carrier
    (`none`/`signature`/`proof`/`either`/`impossible`/`custom`), mirroring
    `cell/src/permissions.rs` and the Rust `dregg_cell::AuthRequired` the firmament's
    `Rights` type re-exports;
  * `Dregg2.Exec.CapTPConcrete.authNarrowerOrEqual` — THE decision
    `granted ⊆ held` (the Rust `is_attenuation` / `AuthRequired::is_narrower_or_equal`,
    clause-for-clause), already proven a genuine partial order (reflexive /
    antisymmetric / transitive, with `impossible` the bottom and `none` the top);
  * `Dregg2.Spec.Authority.Cap` — the `{ target, rights }` capability edge.

The firmament's `Capability::attenuate` (`lib.rs:205`) gates on exactly
`is_attenuation(self.rights, narrower)` — so our `Capability.attenuate` gates on
`authNarrowerOrEqual narrower held`, the SAME predicate, with NO surface/local/
distributed special-casing. The whole point of this module is that "a surface is just
another point on the distance parameter" is a THEOREM, not a slogan.

## What is proven (each mirrors a green Rust test as a Lean theorem)

  1. **ATTENUATE-IS-BACKING-AGNOSTIC** — `attenuate` narrows by the SAME
     `authNarrowerOrEqual` gate regardless of target; a surface cap narrows by the same
     gate as a local/distributed cap (refinement of `Capability::attenuate`, exercised
     by `attenuate_is_backing_agnostic_and_uses_real_check`).
  2. **NO-AMPLIFICATION** — a widening grant (`¬ granted ⊆ held`) is REJECTED for ALL
     three targets, the Surface (window-share) case included (refinement of the
     `FirmamentRouter::attenuate_and_grant` pre-check + `SurfaceBacking::delegate`'s
     executor `DelegationDenied`, exercised by `real_executor_rejects_amplifying_delegate`
     / `real_executor_rejects_widening_surface_share`).
  3. **n = 1 COLLAPSE** — the bounds collapse to strong-local (immediate revoke,
     synchronous commit) at `n = 1` and relax at `n > 1`, while the VERBS are unchanged
     (refinement of `Bounds::distributed` / `Bounds::LOCAL`, exercised by
     `n_equals_one_collapse`; the protocol-level precedent is
     `Dregg2.Distributed.Revocation.single_machine_collapse`).
  4. **SURFACE-RIDES-THE-SAME-GATE** — `Target::Surface` resolves / attenuates /
     delegates through the SAME path as `Distributed` (refinement of the router's
     `Surface`/`Distributed` arms collapsing to one executor turn, `backing_of`
     mapping both to `DistributedTurn`).

NON-VACUITY: both polarities are witnessed (a valid attenuation COMMITS; a widening
REJECTS), at EACH target, via `#guard` teeth that BITE.

Discipline: axiom-clean (`#assert_axioms` at the close) — `decide` / `#guard` / structural
`cases <;> simp` only. `CellId` is the abstract node
identity (NEVER `Nat`), exactly as `Spec.Authority`.
-/
import Dregg2.Exec.CapTPConcrete
import Dregg2.Spec.Authority
import Dregg2.Tactics

namespace Dregg2.Firmament

open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual)

/-! ## §1 — The handle: `Target` (three backings) + `Capability { target, rights }`.

This mirrors `sel4/dregg-firmament/src/lib.rs` (`Target` at `lib.rs:103`, `Capability`
at `lib.rs:169`). `CellId` is the abstract node identity — the cell's value-hash in the
real system, opaque, NEVER `Nat` — exactly as `Spec.Authority` keeps it. `Rights` is the
concrete `AuthReq` carrier the firmament's `Rights = dregg_cell::AuthRequired` type
re-exports. -/

variable {CellId : Type*}

/-- **`Target`** — what a firmament capability points at, and therefore *how far away*
the resource is (the distance `n`) and which backing the router dispatches to. Mirrors
`Target` (`lib.rs:103`):

  * `local slot` — an seL4 kernel object at CNode `slot` (resolved by a syscall;
    revocation synchronous; `n = 1` always);
  * `distributed cell` — a dregg cell on a federation (resolved by a real executor turn;
    revocation = the epoch lift; `n ≥ 1`);
  * `surface cell` — a dregg cell rendered as a window (THE firmament made visual). A
    window IS a capability over a cell, so it resolves by the SAME executor-turn path as
    `distributed`; at `n = 1` (compositor + apps co-located) a surface revoke darkens the
    glass the instant it returns. -/
inductive Target (CellId : Type*) where
  | local (slot : Nat)
  | distributed (cell : CellId)
  | surface (cell : CellId)
  deriving Repr, DecidableEq

namespace Target

/-- Is this target local (resolves via the kernel/stub path)? Mirrors
`Target::is_local` (`lib.rs:151`). -/
def isLocal : Target CellId → Bool
  | .local _ => true
  | _ => false

/-- Is this target a surface — a window, resolving via the executor-turn path (the same
as a distributed cell, since a surface IS a cell)? Mirrors `Target::is_surface`
(`lib.rs:157`). -/
def isSurface : Target CellId → Bool
  | .surface _ => true
  | _ => false

/-- Is this target distributed? (Convenience dual of `isLocal`/`isSurface`.) -/
def isDistributed : Target CellId → Bool
  | .distributed _ => true
  | _ => false

end Target

/-- **`Capability`** — the unified `(target, rights)` handle. ONE handle, three backings.
An app holds it, invokes it, attenuates it (`rights' ⊆ rights`), or delegates it, with
the SAME verbs whatever the target is — the [`router`] is what knows which backing to
dispatch to; the handle itself is backing-agnostic. Mirrors `Capability` (`lib.rs:169`),
with `rights : AuthReq` the concrete dregg lattice (= the Rust `Rights = AuthRequired`).
Structurally a `Spec.Authority.Cap (Target CellId) AuthReq`; we keep a dedicated
structure so the doc and the refinement obligation read against the Rust `Capability`. -/
structure Capability (CellId : Type*) where
  target : Target CellId
  rights : AuthReq
  deriving Repr, DecidableEq

namespace Capability

/-- A handle to a LOCAL kernel object (a CNode slot). Mirrors `Capability::local`
(`lib.rs:178`). (Named `atSlot`, not `local`, since `local` is a Lean keyword; the
`Target.local` *constructor* keeps the name.) -/
def atSlot (slot : Nat) (rights : AuthReq) : Capability CellId :=
  { target := .local slot, rights }

/-- A handle to a DISTRIBUTED dregg cell. Mirrors `Capability::distributed`
(`lib.rs:183`). -/
def distributed (cell : CellId) (rights : AuthReq) : Capability CellId :=
  { target := .distributed cell, rights }

/-- A handle to a SURFACE (a window backed by a dregg cell). "A window =
`Capability { target: Surface(cell), rights }`" made concrete. Mirrors
`Capability::surface` (`lib.rs:193`). -/
def surface (cell : CellId) (rights : AuthReq) : Capability CellId :=
  { target := .surface cell, rights }

/-- **`attenuate cap narrower`** — narrow a handle's rights to `narrower`,
**backing-agnostic**. This is the heart of "adoption is attenuation". It gates on the
REAL `authNarrowerOrEqual narrower (held)` (= `granted ⊆ held`, the Rust
`is_attenuation`) REGARDLESS of `cap.target`, and CLONES the target unchanged — so a
widening is refused identically whether the cap is local, distributed, or surface, and a
narrowing keeps the same target with only the rights moved. Returns `none` if `narrower`
is not `⊆` the held rights.

Mirrors `Capability::attenuate` (`lib.rs:205`): `if !is_attenuation(&self.rights,
&narrower) { return None } else Some(Capability { target: self.target.clone(), rights:
narrower })`. -/
def attenuate (cap : Capability CellId) (narrower : AuthReq) : Option (Capability CellId) :=
  if authNarrowerOrEqual narrower cap.rights then
    some { target := cap.target, rights := narrower }
  else
    none

end Capability

/-! ## §2 — The `n`-parametrized bounds and their `n = 1` collapse.

This mirrors `Bounds` (`lib.rs:220`) + `Bounds::LOCAL` (`lib.rs:236`) +
`Bounds::distributed` (`lib.rs:240`). The bounds are the ONLY thing that slides along the
distance parameter; the verbs are identical at every `n`. -/

/-- **`Bounds`** — the honest distance-bounds that held for an operation. `n` is the
number of machines the target is spread across; `revocationImmediate` /
`commitSynchronous` are the strong properties that hold at `n = 1`. Mirrors `Bounds`
(`lib.rs:220`). -/
structure Bounds where
  revocationImmediate : Bool
  commitSynchronous : Bool
  n : Nat
  deriving Repr, DecidableEq

namespace Bounds

/-- The strong `n = 1` bounds: immediate revocation, synchronous commit — the
firmament's headline guarantees for a local deployment. Mirrors `Bounds::LOCAL`
(`lib.rs:236`). (Named `strongLocal`, not `local`, since `local` is a Lean keyword.) -/
def strongLocal : Bounds := { revocationImmediate := true, commitSynchronous := true, n := 1 }

/-- The bounds for a distributed target spread across `n` machines. At `n ≤ 1` a
distributed target that happens to be on THIS machine collapses to the strong local
bounds — the `n = 1` collapse, exactly; at `n > 1` both relax (eventual revocation,
quorum commit). Mirrors `Bounds::distributed` (`lib.rs:240`). -/
def distributed (n : Nat) : Bounds :=
  if n ≤ 1 then
    Bounds.strongLocal
  else
    { revocationImmediate := false, commitSynchronous := false, n }

/-- Are these the strong local bounds (both strong properties hold)? -/
def isStrongLocal (b : Bounds) : Bool := b.revocationImmediate && b.commitSynchronous

end Bounds

/-! ## §3 — Backings and the router dispatch.

The router (`sel4/dregg-firmament/src/router.rs`) looks ONLY at the handle's `Target` to
decide which backing resolves it: `Local` → the kernel (`LocalKernel`); `Distributed`
AND `Surface` → a real executor turn (`DistributedTurn`) — a surface IS a cell, so it
rides the same backing. We model the dispatch as a total function on `Target`. -/

/-- **`Backing`** — which backing resolved an invocation. Purely informational: the app
does NOT branch on it (the whole point is that it cannot tell). Mirrors `Backing`
(`lib.rs:270`): `LocalKernel` / `DistributedTurn`. -/
inductive Backing where
  | localKernel
  | distributedTurn
  deriving Repr, DecidableEq

/-- **`backingOf cap`** — which backing WOULD resolve this handle, by target alone.
Mirrors `FirmamentRouter::backing_of` (`router.rs:211`): a local target resolves via the
kernel; a distributed cell AND a surface (which IS a cell) both resolve via a real
executor turn — so the surface and distributed arms map to the SAME backing. -/
def backingOf (cap : Capability CellId) : Backing :=
  match cap.target with
  | .local _ => Backing.localKernel
  | .distributed _ => Backing.distributedTurn
  | .surface _ => Backing.distributedTurn

/-- **`boundsOf cap n`** — the bounds the router records for resolving `cap` at distance
`n`. A LOCAL target is always `Bounds.strongLocal` (a kernel object is on this box; the
`LocalBacking::invoke` returns `Bounds::LOCAL`, `local.rs:93`). A DISTRIBUTED or SURFACE
target gets the `n`-parametrized `Bounds.distributed n` (`distributed.rs:124`,
`surface.rs:147`) — collapsing to local at `n ≤ 1`. -/
def boundsOf (cap : Capability CellId) (n : Nat) : Bounds :=
  match cap.target with
  | .local _ => Bounds.strongLocal
  | .distributed _ => Bounds.distributed n
  | .surface _ => Bounds.distributed n

/-! ## §4 — The router's authority gate, factored out (the ONE check, all targets).

Every backing's `invoke`/`delegate` ultimately gates on the SAME `granted ⊆ held`
(`local.rs:85`, `distributed.rs:116`, `surface.rs:139`, and the executor's
`DelegationDenied` for the delegate path). We name that single decision and route ALL
three targets through it, so "no special-casing" is structural. -/

/-- **`grantOk held granted`** — the ONE non-amplification decision the firmament gate
runs, for ANY target: `granted ⊆ held`, i.e. `authNarrowerOrEqual granted held`. This is
the Rust `is_attenuation(&held, &granted)` (`lib.rs:209`, re-exported from
`dregg_cell::is_attenuation`), and the executor's grant gate (`DelegationDenied`
otherwise). NOTE the argument order: `authNarrowerOrEqual` takes the narrower first, so
`grantOk held granted = authNarrowerOrEqual granted held`. -/
def grantOk (held granted : AuthReq) : Bool := authNarrowerOrEqual granted held

/-- **`routerAttenuateGrant cap narrower`** — the backing-agnostic pre-check the router's
`attenuate_and_grant` runs FIRST, for EVERY target (`router.rs:141`): it calls
`cap.attenuate(narrower)`, refusing a widening before it ever touches a backing. We model
exactly that: the result is the narrowed handle, or `none` if `narrower ⊄ held`. The
backing then re-checks (defense in depth), but the gate is this one predicate — the same
for local/distributed/surface. -/
def routerAttenuateGrant (cap : Capability CellId) (narrower : AuthReq) :
    Option (Capability CellId) :=
  cap.attenuate narrower

/-! ## §5 — THEOREM 1: ATTENUATE-IS-BACKING-AGNOSTIC.

`attenuate` narrows by the SAME `authNarrowerOrEqual` gate REGARDLESS of target. We prove
the decision and the resulting handle are functions of the rights alone, with the target
carried through unchanged — so a surface cap narrows by the SAME gate as a local or
distributed cap, with no special-casing.

Refinement obligation FOR: `Capability::attenuate` (`lib.rs:205`) — exercised by the Rust
test `attenuate_is_backing_agnostic_and_uses_real_check` (`lib.rs:302`). -/

/-- The attenuation **decision** depends ONLY on the rights, never the backing: for ANY
two targets `t₁ t₂` and any held rights `r`, `attenuate` succeeds on `⟨t₁, r⟩` iff it
succeeds on `⟨t₂, r⟩`. The gate is `authNarrowerOrEqual narrower r` either way — backing
is invisible to it. -/
theorem attenuate_decision_backing_agnostic
    (t₁ t₂ : Target CellId) (r narrower : AuthReq) :
    (Capability.attenuate ⟨t₁, r⟩ narrower).isSome
      = (Capability.attenuate ⟨t₂, r⟩ narrower).isSome := by
  simp only [Capability.attenuate]
  cases authNarrowerOrEqual narrower r <;> simp

/-- When attenuation succeeds, it **carries the target through unchanged** — only the
rights move (`self.target.clone()` in the Rust). So narrowing a surface handle yields a
surface handle over the SAME cell; narrowing a local handle yields a local handle at the
SAME slot. -/
theorem attenuate_preserves_target
    (cap : Capability CellId) (narrower : AuthReq) (out : Capability CellId)
    (h : cap.attenuate narrower = some out) :
    out.target = cap.target ∧ out.rights = narrower := by
  simp only [Capability.attenuate] at h
  by_cases hn : authNarrowerOrEqual narrower cap.rights
  · simp [hn] at h; subst h; exact ⟨rfl, rfl⟩
  · simp [hn] at h

/-- The decision is LITERALLY the dregg lattice gate `granted ⊆ held` — `attenuate`
succeeds iff `authNarrowerOrEqual narrower held = true`. The Rust `is_attenuation`, no
reinvention, no per-target branch. -/
theorem attenuate_iff_grantOk (cap : Capability CellId) (narrower : AuthReq) :
    (cap.attenuate narrower).isSome = true ↔ grantOk cap.rights narrower = true := by
  simp only [Capability.attenuate, grantOk]
  cases authNarrowerOrEqual narrower cap.rights <;> simp

/-! ## §6 — THEOREM 2: NO-AMPLIFICATION (all three targets, surface included).

A widening grant (`¬ granted ⊆ held`) is REJECTED for ALL three targets. We prove the
router pre-check `routerAttenuateGrant` returns `none` on a widening for a local, a
distributed, AND a surface handle — the Surface (window-share) case included: a widening
window-share is refused, no-amplification at the glass.

Refinement obligation FOR: `FirmamentRouter::attenuate_and_grant`'s backing-agnostic
pre-check (`router.rs:141`) + each backing's executor re-check
(`SurfaceBacking::delegate` `DelegationDenied`, `surface.rs:220`;
`DistributedBacking::delegate`, `distributed.rs:196`; `LocalBacking::mint` refusal,
`local.rs:108`) — exercised by `real_executor_rejects_amplifying_delegate`
(`distributed.rs:254`) and `real_executor_rejects_widening_surface_share`
(`surface.rs:279`). -/

/-- **The general no-amplification law.** For ANY target, if the grant is NOT an
attenuation (`grantOk held narrower = false`), the router's attenuate-grant pre-check
REFUSES it (`none`). One statement, quantified over `t : Target CellId`, so it holds
uniformly for local / distributed / surface. -/
theorem no_amplification
    (t : Target CellId) (held narrower : AuthReq)
    (hwiden : grantOk held narrower = false) :
    routerAttenuateGrant ⟨t, held⟩ narrower = none := by
  simp only [routerAttenuateGrant, Capability.attenuate, grantOk] at *
  simp [hwiden]

/-- **No-amplification at the SURFACE specifically** — a widening window-share is refused.
The headline desktop case of `no_amplification`: handing out MORE authority over the
glass than you hold (e.g. promoting a read-only mirror, `signature`, to a fully-authorized
surface, `none`) is rejected. This is the no-amplification guarantee firing at the
*pixel* layer. -/
theorem no_amplification_surface
    (cell : CellId) (held narrower : AuthReq)
    (hwiden : grantOk held narrower = false) :
    routerAttenuateGrant (Capability.surface cell held) narrower = none :=
  no_amplification (.surface cell) held narrower hwiden

/-- **Dually, a genuine attenuation COMMITS at any target** (the positive polarity): if
`grantOk held narrower = true`, the pre-check yields the narrowed handle, over the SAME
target, with the narrowed rights. Non-vacuity at the law level: the gate is not
constantly-`none`. -/
theorem attenuating_grant_commits
    (t : Target CellId) (held narrower : AuthReq)
    (hatten : grantOk held narrower = true) :
    routerAttenuateGrant ⟨t, held⟩ narrower = some ⟨t, narrower⟩ := by
  simp only [routerAttenuateGrant, Capability.attenuate, grantOk] at *
  simp [hatten]

/-! ## §7 — THEOREM 3: the `n = 1` COLLAPSE (bounds slide, verbs do not).

The bounds collapse to strong-local (immediate revoke, synchronous commit) at `n = 1`
and relax at `n > 1`, while the VERBS are unchanged. We prove `boundsOf` for a distributed
/ surface target equals `Bounds.strongLocal` at `n = 1`, relaxes at `n > 1`, AND that the
router dispatch (`backingOf`) is INDEPENDENT of `n` — the distance parameter slides the
bounds, not the semantics.

Refinement obligation FOR: `Bounds::distributed` / `Bounds::LOCAL` (`lib.rs:240`/`236`)
and the bounds the backings record (`distributed.rs:124`, `surface.rs:147`) — exercised
by `n_equals_one_collapse` (`lib.rs:325`). Protocol-level precedent:
`Dregg2.Distributed.Revocation.single_machine_collapse`. -/

/-- At `n = 1`, `Bounds.distributed` collapses to the strong local bounds. -/
theorem distributed_collapses_at_one : Bounds.distributed 1 = Bounds.strongLocal := by
  decide

/-- The collapsed bounds ARE strong-local: immediate revocation AND synchronous commit. -/
theorem collapse_is_strong_local :
    (Bounds.distributed 1).revocationImmediate = true
      ∧ (Bounds.distributed 1).commitSynchronous = true := by
  decide

/-- At `n > 1` the bounds RELAX — revocation is no longer immediate and commit no longer
synchronous (the eventual epoch lift, the quorum latency). Witnessed at `n = 5`. -/
theorem bounds_relax_above_one :
    (Bounds.distributed 5).revocationImmediate = false
      ∧ (Bounds.distributed 5).commitSynchronous = false
      ∧ (Bounds.distributed 5).n = 5 := by
  decide

/-- **The collapse holds for a SURFACE target specifically**: a surface resolved at
`n = 1` gets the strong local bounds (a surface revoke is immediate — the window goes
dark the instant the syscall returns), and at `n > 1` (a remote window over the wire) the
bounds relax. The same collapse the distributed cell gets — a surface is just another
point on `n`. -/
theorem surface_bounds_collapse (cell : CellId) :
    boundsOf (Capability.surface cell .either) 1 = Bounds.strongLocal
      ∧ (boundsOf (Capability.surface cell .either) 5).revocationImmediate = false := by
  refine ⟨?_, ?_⟩ <;> simp only [boundsOf, Capability.surface] <;> decide

/-- **The VERBS are unchanged as `n` slides** — the router dispatch (`backingOf`) does
NOT depend on `n` at all (it is a function of the target alone). For a distributed/surface
cap whose bounds genuinely DIFFER between two distances `n₁ < n₂` straddling the collapse
(`n₁ = 1`, `n₂ > 1`), the backing the invocation routes to is nonetheless IDENTICAL. This
is "the distance parameter slides the bounds, not the semantics" as a theorem: the bounds
move, the verb does not. -/
theorem verbs_independent_of_n (cell : CellId) :
    -- the verb (backing) is the SAME at n=1 and n=5 …
    backingOf (Capability.distributed cell .either)
        = backingOf (Capability.distributed cell .either)
    -- … even though the BOUNDS differ across that collapse boundary.
    ∧ boundsOf (Capability.distributed cell .either) 1
        ≠ boundsOf (Capability.distributed cell .either) 5 := by
  refine ⟨rfl, ?_⟩
  simp only [boundsOf, Capability.distributed]
  decide

/-- Sharper form of "verbs unchanged": for a surface (or distributed) target the BACKING
is `distributedTurn` at EVERY `n`, while the BOUNDS differ between `n = 1` and `n = 5`.
Same verb, different bounds — the collapse is in the bounds only. -/
theorem surface_same_verb_different_bounds (cell : CellId) :
    backingOf (Capability.surface cell .either) = Backing.distributedTurn
      ∧ boundsOf (Capability.surface cell .either) 1
          ≠ boundsOf (Capability.surface cell .either) 5 := by
  refine ⟨rfl, ?_⟩
  simp only [boundsOf, Capability.surface]
  decide

/-! ## §8 — THEOREM 4: SURFACE-RIDES-THE-SAME-GATE (a surface is another point on `n`).

`Target::Surface` resolves / attenuates / delegates through the SAME path as
`Distributed`. We prove: (a) the router backing for a surface EQUALS the backing for a
distributed cell (both `distributedTurn`); (b) the attenuation gate is the SAME predicate
for a surface as for a distributed cell over the same rights; (c) the bounds function is
the SAME for a surface as for a distributed cell at every `n`. So the surface arm is the
distributed arm, aimed at the glass — "a surface is just another point on the distance
parameter" is a theorem.

Refinement obligation FOR: the router collapsing its `Surface` and `Distributed` arms to
one executor-turn path (`router.rs:120`/`178` both call the real-turn backing;
`backing_of` `router.rs:211` maps both to `DistributedTurn`) and `SurfaceBacking` BEING
`DistributedBacking` aimed at a surface cell (`surface.rs` docstring) — exercised by the
shape of `real_executor_enforces_attenuation_on_surface_share` (`surface.rs:257`)
matching `real_executor_enforces_attenuation_on_delegate` (`distributed.rs:232`). -/

/-- **(a) Same BACKING.** A surface and a distributed cell route to the IDENTICAL backing
(`distributedTurn`) — the surface arm IS the distributed arm. -/
theorem surface_backing_eq_distributed (c d : CellId) :
    backingOf (Capability.surface c .either) = backingOf (Capability.distributed d .either) := by
  rfl

/-- A surface NEVER routes to the local-kernel backing — it always goes through the real
executor turn, exactly like a distributed cell (and unlike a local kernel object). -/
theorem surface_is_not_local_backing (c : CellId) :
    backingOf (Capability.surface c .either) ≠ Backing.localKernel := by
  simp [backingOf, Capability.surface]

/-- **(b) Same GATE.** Over the same held + requested rights, the attenuation decision is
the SAME for a surface handle and a distributed handle — both reduce to
`authNarrowerOrEqual narrower r`. No surface-specific authority is invented; the
compositor multiplexes capabilities, it does not mint authority. -/
theorem surface_gate_eq_distributed (c d : CellId) (r narrower : AuthReq) :
    (Capability.attenuate (Capability.surface c r) narrower).isSome
      = (Capability.attenuate (Capability.distributed d r) narrower).isSome :=
  attenuate_decision_backing_agnostic _ _ r narrower

/-- **(c) Same BOUNDS.** At EVERY distance `n`, a surface target and a distributed target
get the IDENTICAL bounds (`Bounds.distributed n`). The surface slides along `n` by the
same rule as the distributed cell. -/
theorem surface_bounds_eq_distributed (c d : CellId) (n : Nat) :
    boundsOf (Capability.surface c .either) n = boundsOf (Capability.distributed d .either) n := by
  rfl

/-- **The keystone, assembled: SURFACE ≡ DISTRIBUTED on all three axes** (backing, gate,
bounds) — the single statement that "a surface is just another point on the distance
parameter." It is the same verb path (backing), the same `granted ⊆ held` gate, and the
same `n`-parametrized bounds as a distributed cell; the ONLY thing that distinguishes a
surface is that the compositor renders its cell-state as glass. -/
theorem surface_is_another_point_on_n
    (c d : CellId) (r narrower : AuthReq) (n : Nat) :
    -- same backing (verb path)
    backingOf (Capability.surface c r) = backingOf (Capability.distributed d r)
    -- same attenuation gate
    ∧ (Capability.attenuate (Capability.surface c r) narrower).isSome
        = (Capability.attenuate (Capability.distributed d r) narrower).isSome
    -- same n-parametrized bounds
    ∧ boundsOf (Capability.surface c r) n = boundsOf (Capability.distributed d r) n := by
  refine ⟨rfl, ?_, rfl⟩
  exact attenuate_decision_backing_agnostic _ _ r narrower

/-! ## §9 — NON-VACUITY TEETH (`#guard`): both polarities BITE, at each target.

The lattice (from `Exec.CapTPConcrete`, mirroring the Rust): `none` is the top (broadest),
`either` is below it, `signature`/`proof` below `either`, `impossible` the bottom. So
`either → signature` is a NARROWING (commits) and `signature → either` /
`signature → none` are WIDENINGS (reject); `signature → impossible` is a narrowing
(commits). We pin a CONCRETE `CellId := Nat` ONLY for these executable `#guard` witnesses
(the theorems above stay `CellId`-abstract); a `Nat` cell-id is fine for a witness, it is
never load-bearing in a proof.

These are the Lean mirrors of the green Rust tests:
`attenuate_is_backing_agnostic_and_uses_real_check`,
`real_executor_rejects_amplifying_delegate`,
`real_executor_enforces_attenuation_on_surface_share`,
`real_executor_rejects_widening_surface_share`, `n_equals_one_collapse`. -/

section Witnesses

/-- A concrete cell-id carrier for the executable witnesses ONLY (never used in a proof). -/
abbrev WCell := Nat

/-! ### ATTENUATE-IS-BACKING-AGNOSTIC — a genuine narrowing COMMITS at every target; the
SAME narrowing yields the SAME rights (target-agnostic). -/

-- COMMITS: `either → signature` narrows, at local / distributed / surface alike.
#guard (Capability.atSlot (CellId := WCell) 3 .either |>.attenuate .signature).isSome
#guard (Capability.distributed (7 : WCell) .either |>.attenuate .signature).isSome
#guard (Capability.surface (7 : WCell) .either |>.attenuate .signature).isSome

-- The narrowed rights are identical across backings (backing-agnostic), and the target is
-- carried through (a surface stays a surface over the same cell).
#guard (Capability.atSlot (CellId := WCell) 3 .either |>.attenuate .signature)
  == some (Capability.atSlot 3 .signature)
#guard (Capability.distributed (7 : WCell) .either |>.attenuate .signature)
  == some (Capability.distributed 7 .signature)
#guard (Capability.surface (7 : WCell) .either |>.attenuate .signature)
  == some (Capability.surface 7 .signature)

/-! ### NO-AMPLIFICATION — a widening REJECTS at every target, the SURFACE included. -/

-- REJECTS: `signature → either` is a widening (either is broader), at all three targets.
#guard (Capability.atSlot (CellId := WCell) 3 .signature |>.attenuate .either).isNone
#guard (Capability.distributed (7 : WCell) .signature |>.attenuate .either).isNone
#guard (Capability.surface (7 : WCell) .signature |>.attenuate .either).isNone

-- REJECTS: `signature → none` is the maximal widening (none is the top), surface included
-- (the headline "widening window-share refused" — no-amplification at the glass).
#guard (Capability.surface (7 : WCell) .signature |>.attenuate .none).isNone
#guard (routerAttenuateGrant (Capability.surface (7 : WCell) .signature) .none).isNone

-- COMMITS: `signature → impossible` narrows (impossible is the bottom), surface included —
-- the OTHER polarity, so the surface gate is not constantly-`none`.
#guard (Capability.surface (7 : WCell) .signature |>.attenuate .impossible).isSome
#guard (routerAttenuateGrant (Capability.surface (7 : WCell) .signature) .impossible)
  == some (Capability.surface 7 .impossible)

/-! ### n = 1 COLLAPSE — strong-local at n=1, relaxed above, for distributed AND surface. -/

#guard Bounds.distributed 1 == Bounds.strongLocal
#guard (Bounds.distributed 1).revocationImmediate
#guard (Bounds.distributed 1).commitSynchronous
#guard (Bounds.distributed 1).isStrongLocal
-- Above 1 the bounds relax (the verbs do not — see backing pins below).
#guard !(Bounds.distributed 5).revocationImmediate
#guard !(Bounds.distributed 5).commitSynchronous
#guard !(Bounds.distributed 5).isStrongLocal
-- A surface collapses to strong-local at n=1 and relaxes at n=5.
#guard boundsOf (Capability.surface (7 : WCell) .either) 1 == Bounds.strongLocal
#guard !(boundsOf (Capability.surface (7 : WCell) .either) 5).revocationImmediate

/-! ### SURFACE-RIDES-THE-SAME-GATE — surface backing/gate/bounds ≡ distributed. -/

-- Same BACKING: surface and distributed both route to `distributedTurn`; surface is NOT
-- the local-kernel backing.
#guard backingOf (Capability.surface (7 : WCell) .either) == Backing.distributedTurn
#guard backingOf (Capability.surface (7 : WCell) .either)
  == backingOf (Capability.distributed (9 : WCell) .either)
#guard backingOf (Capability.atSlot (CellId := WCell) 3 .either) == Backing.localKernel
-- Same VERB, different BOUNDS across n (the collapse is in the bounds only).
#guard backingOf (Capability.surface (7 : WCell) .either)
  == backingOf (Capability.surface (7 : WCell) .either)  -- backing is n-independent
#guard boundsOf (Capability.surface (7 : WCell) .either) 1
  != boundsOf (Capability.surface (7 : WCell) .either) 5  -- bounds are not
-- Same GATE: the same narrowing decision for surface as for distributed over same rights.
#guard (Capability.surface (7 : WCell) .either |>.attenuate .signature).isSome
  == (Capability.distributed (9 : WCell) .either |>.attenuate .signature).isSome
#guard (Capability.surface (7 : WCell) .signature |>.attenuate .either).isSome
  == (Capability.distributed (9 : WCell) .signature |>.attenuate .either).isSome

end Witnesses

/-! ## §10 — Axiom hygiene. Every load-bearing theorem is checked axiom-clean (only the
standard `propext`/`Classical.choice`/`Quot.sound`). -/

#assert_axioms attenuate_decision_backing_agnostic
#assert_axioms attenuate_preserves_target
#assert_axioms attenuate_iff_grantOk
#assert_axioms no_amplification
#assert_axioms no_amplification_surface
#assert_axioms attenuating_grant_commits
#assert_axioms distributed_collapses_at_one
#assert_axioms collapse_is_strong_local
#assert_axioms bounds_relax_above_one
#assert_axioms verbs_independent_of_n
#assert_axioms surface_bounds_collapse
#assert_axioms surface_same_verb_different_bounds
#assert_axioms surface_backing_eq_distributed
#assert_axioms surface_is_not_local_backing
#assert_axioms surface_gate_eq_distributed
#assert_axioms surface_bounds_eq_distributed
#assert_axioms surface_is_another_point_on_n

end Dregg2.Firmament
