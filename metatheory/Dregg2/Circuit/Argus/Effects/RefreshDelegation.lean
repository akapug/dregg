/-
# Dregg2.Circuit.Argus.Effects.RefreshDelegation — the DELEGATION-SNAPSHOT effect `refreshDelegationA`
welded into the Argus IR, on the FULL-STATE `Surface2` surface.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn (single-cell moves). `Argus/Effects/BalanceA.lean` is the FULL-STATE template: it
welds a v2 `EffectCommit2`/`Surface2` `*_full_sound` (concluding the WHOLE post-state) by routing the
executor side through a chained-executor lift + an independent executor⟺spec corner. This module replays
THAT (stronger) template for the different **cap-graph / delegation-snapshot** effect
`refreshDelegationA`, in a disjoint file (it imports the Argus IR + the audited `refreshDelegationA` v2
instance read-only and owns only its own declarations; it edits no other Argus module).

## What `refreshDelegationA` does (the kernel step the cornerstone pins)

`refreshDelegationA` is the SELF-only delegation refresh (dregg1 `apply_refresh_delegation`,
`apply.rs:2991`): a child re-snapshots its parent's CURRENT c-list. The chained kernel arm is
`refreshDelegationChainA` (`TurnExecutorFull.lean:1761`), which `execFullA` routes to
(`TurnExecutorFull.lean:3897`). FAIL-CLOSED on a TWO-conjunct gate — the self-authority gate
(`stateAuthB actor child`, dregg1's self-only `action_target == child`) AND the child having a
parent (`(delegate child).isSome`, dregg1's `delegate.ok_or_else`, `apply.rs:3004`). On commit it
OVERWRITES `delegations child` with a FRESH snapshot of the parent's CURRENT `caps` (`parentClist`),
prepends a self-targeted receipt row, and FREEZES the other 16 `RecordKernelState` fields. Balance-neutral.

Because it touches the per-cell `delegations : CellId → List Cap` registry (NOT `cell`/`bal`/`caps`), the
IR body's move is the §A `setDelegations` write-primitive (`Stmt.lean:71`) — the FIRST weld to use it. The
gate is a bare guard over those two conjuncts. Unlike `BalanceA` (whose chained executor adds a 7th
`acceptsEffects` dst-liveness conjunct ON TOP of the raw kernel gate), the refresh CHAINED gate is
IDENTICAL to the kernel-step gate (`refreshDelegationChainA` has no `acceptsEffects` pre-gate) — so the
chained lift carries NO extra side-condition (a cleaner lift than BalanceA's).

## THE DESCRIPTOR (the full-state crown jewel — read this)

`refreshDelegationA` carries a GENUINE standalone full-state circuit⟺spec descriptor in the v2
EffectCommit2 / `Surface2` universe (`Dregg2/Circuit/Inst/refreshDelegationA.lean`):

  * `refreshDelegationE D hD` — the `EffectSpec2` whose touched component is the WHOLE `delegations`
    FUNCTION, digested by a `funcComponent` (`D : (CellId → List Cap) → ℤ`, `Function.Injective D`); its
    `restFrame` freezes the other 16 kernel fields and its `logUpdate` is the receipt prepend.
  * `refreshDelegationA_full_sound : satisfiedE2 S (refreshDelegationE D hD) (encodeE2 …) ⟹
    RefreshDelegationSpec` — a FULL 17-field declarative post-state soundness (`Spec/refreshdelegation.lean`),
    keyed on the chained executor via the independent `refreshDelegation_iff_spec` (executor ⟺ spec, BOTH
    directions, full state).

This module covers both directions, exactly as BalanceA:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_refreshDelegationStmt_eq_refreshDelegationStep`
      — the kernel step IS the Argus term, using `setDelegations`. New, standalone, the delegation-snapshot
      analog of `interp_balanceAStmt_eq_recKExecAsset`.

  (2) **Compile weld against refreshDelegationA's OWN full-state descriptor:** lift the kernel cornerstone
      to the chained `execFullA` (NO side-condition — the gate is identical), then weld to
      `refreshDelegationA_full_sound`. The conclusion is the FULL `RefreshDelegationSpec` agreement (all 17
      kernel fields + the receipt log) — a satisfying witness of refresh's own circuit agrees with the WHOLE
      post-state the IR term's executor produces. The FULL-STATE Surface2 surface (strictly stronger than a
      per-cell EffectVM projection).

## SURFACE + THE REPORTED KERNEL-vs-RUNTIME DIVERGENCE (precise — do NOT over-read)

  * **FULL-STATE Surface2 (not per-cell).** The conclusion is `st' = { kernel := k', log := receipt :: log }`
    — the WHOLE chained post-state, because `RefreshDelegationSpec` pins every one of the 17 kernel fields
    plus the log. This is the same surface BalanceA's `balanceA_compile_sound` reaches, on the delegation
    registry. The descriptor digests the `delegations` FUNCTION (a `funcComponent` whole-function digest);
    so the circuit binds the function up to `D`'s injectivity, the faithful digest-not-list boundary.

  * **THE DIGEST BOUNDARY.** The circuit carries the `delegations` post-state as a SCALAR `funcComponent`
    digest `D (refreshDelegationsMap …)`, not the function literally. The full-state agreement holds because
    BOTH the circuit-side soundness AND the executor-side `refreshDelegation_iff_spec` name the SAME
    `RefreshDelegationSpec`, whose `delegations` clause IS the function equality; the realizability of `D`
    (`Function.Injective D`) enters ONLY inside the reused `refreshDelegationA_full_sound`, not in the welded
    conclusion's statement.

  * **THE REPORTED DIVERGENCE — kernel step vs full Rust RUNTIME (the `delegation_epoch` root-gap).** The
    Rust runtime's `RefreshDelegation` action also bumps a `delegation_epoch` counter (a freshness witness
    the runtime tracks); the Lean kernel step models the SNAPSHOT overwrite but NOT an epoch counter
    (`RecordKernelState` has no `delegation_epoch` field). So on the epoch witness the Lean kernel step is a
    STRICT UNDER-MODEL of the Rust runtime — the same flagged cap-revocation/refresh root-gap as the sibling
    `RevokeDelegation` weld. This is reported, not papered, as `refreshKernel_undermodels_runtime_epoch` (a
    documentation theorem pinning the model carries no epoch field — the `delegate` parent pointer is frozen,
    so no monotone epoch is tracked), so the gap cannot silently regress. Closing it is a kernel-model
    widening (add a `delegationEpoch` registry to the kernel + re-derive the descriptor), out of scope.

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the
whole-function-digest assumption enters ONLY inside the reused `refreshDelegationA_full_sound` (its
`Function.Injective D` hypothesis), not in the welded conclusion's statement. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Exec.Handlers.Lifecycle

namespace Dregg2.Circuit.Argus.Effects.RefreshDelegation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec.Handlers.Lifecycle (refreshDelegationStep RefreshDelegationArgs)
-- Broad opens mirroring `Inst/refreshDelegationA.lean` so the standalone-descriptor names resolve
-- unqualified: `logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in
-- `EffectCommit2`; the spec + its executor⟺spec corner in `Spec.RefreshDelegation`; the descriptor +
-- its full soundness in `Inst.RefreshDelegationA`.
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.RefreshDelegation
  (RefreshDelegationSpec RefreshDelegationFullSpec RefreshDelegationGuard refreshDelegationsMap
   refreshEpochAtMap refreshDelegationReceipt refreshDelegation_iff_spec)
open Dregg2.Exec.TurnExecutorFull (parentEpoch)
open Dregg2.Circuit.Inst.RefreshDelegationA
  (RestIffNoDelegations refreshDelegationE refreshDelegationA_full_sound)
open Dregg2.Authority (Caps Cap)

/-! ## §1 — The refreshDelegation effect as an Argus IR term (gate, then the `setDelegations` snapshot).

The kernel step `refreshDelegationStep k ⟨actor, child⟩` (`Handlers/Lifecycle.lean:67`) is
`if stateAuthB k.caps actor child && (k.delegate child).isSome then some { k with delegations := … } else
none`, where the post-`delegations` is `fun c => if c = child then parentClist k child else k.delegations c`
— EXACTLY the declarative `refreshDelegationsMap k child` (`Spec/refreshdelegation.lean:30`). We capture
it term-for-term: a `Bool` `guard` of the EXACT two conjuncts, then a `setDelegations` whose leaf is
`refreshDelegationsMap`. The contrast with transfer/mint/burn is the move primitive: `setDelegations`
(rewrites the per-cell `delegations` registry) over `refreshDelegationsMap` (the self-targeted parent
snapshot), NOT `setCell`/`recTransfer`. -/

/-- The refreshDelegation admissibility gate as a `Bool` — exactly `refreshDelegationStep`'s `if` (the two
conjuncts: self-authority over `child`, and `child` having a parent). The kernel gate is
IDENTICAL to the chained `refreshDelegationChainA` gate (no `acceptsEffects` pre-gate is added). -/
def refreshDelegationGuard (actor child : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor child && (k.delegate child).isSome

/-- **The refreshDelegation effect as an IR term: gate, then snapshot the parent c-list.** Mirrors
`transferStmt` (gate, then move) but the move is `setDelegations` over `refreshDelegationsMap` — the
self-targeted overwrite of the per-cell `delegations` registry with the parent's CURRENT c-list — NOT
`setCell` over `recTransfer`. The `setDelegations` leaf is `refreshDelegationsMap k child`, EXACTLY the
post-`delegations` `refreshDelegationStep` installs. -/
def refreshDelegationStmt (actor child : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (refreshDelegationGuard actor child))
    (RecStmt.setDelegations (fun k => refreshDelegationsMap k child))

/-! ## §2 — The cornerstone: `interp` of the refreshDelegation term IS the kernel step
`refreshDelegationStep`. -/

/-- The refreshDelegation `Bool` gate decodes to `refreshDelegationStep`'s admissibility proposition (the
two conjuncts, in the SAME order the kernel `if` checks them). The delegation-snapshot analog of
`balanceAGuard_iff`. -/
theorem refreshDelegationGuard_iff (actor child : CellId) (k : RecordKernelState) :
    refreshDelegationGuard actor child k = true ↔
      (stateAuthB k.caps actor child = true ∧ (k.delegate child).isSome = true) := by
  simp only [refreshDelegationGuard, Bool.and_eq_true]

/-- **The cornerstone (delegation snapshot).** `interp` of the refreshDelegation term IS the verified
kernel step `refreshDelegationStep` — the same partial function, by construction, exactly as the transfer
cornerstone, now over the per-cell `delegations` registry via `setDelegations`/`refreshDelegationsMap`
(NOT the record-cell `setCell`/`recTransfer`). The executor IS the meaning of the term. -/
theorem interp_refreshDelegationStmt_eq_refreshDelegationStep (actor child : CellId)
    (k : RecordKernelState) :
    interp (refreshDelegationStmt actor child) k
      = refreshDelegationStep k { actor := actor, child := child } := by
  -- both the IR-term's `guard` predicate (`refreshDelegationGuard`) and the kernel step's `if`-condition
  -- are the SAME Bool `stateAuthB k.caps actor child && (k.delegate child).isSome`. Unfold both, then a
  -- single `by_cases` on that shared gate discharges both arms; the committed `delegations` write is
  -- `refreshDelegationsMap k child` on both sides (definitional).
  simp only [refreshDelegationStmt, interp, refreshDelegationGuard]
  unfold refreshDelegationStep
  by_cases hg : (stateAuthB k.caps actor child && (k.delegate child).isSome) = true
  · rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos hg]
    -- the IR `setDelegations` leaf is `refreshDelegationsMap k child`, which UNFOLDS to the kernel step's
    -- inline `fun c => if c = child then parentClist k child else k.delegations c` — definitionally equal.
    rfl
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg hg]

#assert_axioms interp_refreshDelegationStmt_eq_refreshDelegationStep

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `refreshDelegationChainA` / `execFullA`.

The standalone refreshDelegation descriptor (§4) is keyed on the CHAINED executor `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.refreshDelegationA actor child) =
refreshDelegationChainA s actor child` (`TurnExecutorFull.lean:3897`). The §2 cornerstone is over the
kernel step `refreshDelegationStep`. The chained layer is exactly `refreshDelegationStep` on the kernel
PLUS the receipt-log prepend `receipt :: s.log` — and, crucially, the SAME two-conjunct gate (no extra
`acceptsEffects` pre-gate, unlike BalanceA). We bridge faithfully, carrying NO side-condition: when the §2
cornerstone commits on the kernel, the chained executor commits with the receipt prepended. -/

/-- **`interp_refreshDelegationStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits the FROZEN-FACE kernel step (`interp (refreshDelegationStmt actor child)
st.kernel = some k'`, the `delegations` snapshot only), the unified action executor `execFullA st
(.refreshDelegationA actor child)` commits to the chained state `⟨k' WITH the freshness-restore epoch
stamp, refreshDelegationReceipt actor child :: st.log⟩`. The IR term models the frozen face; the FAITHFUL
chained executor ALSO re-stamps `delegationEpochAt` (`refreshEpochAtMap`), carried here as the named
epoch-stamp residual ON TOP of the frozen `k'`. -/
theorem interp_refreshDelegationStmt_chained
    (st : RecChainedState) (actor child : CellId) (k' : RecordKernelState)
    (hexec : interp (refreshDelegationStmt actor child) st.kernel = some k') :
    execFullA st (.refreshDelegationA actor child)
      = some { kernel := { k' with delegationEpochAt := refreshEpochAtMap st.kernel child },
               log := refreshDelegationReceipt actor child :: st.log } := by
  -- the §2 cornerstone turns the IR term into the FROZEN-FACE kernel step `refreshDelegationStep`.
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep] at hexec
  show refreshDelegationChainA st actor child
      = some { kernel := { k' with delegationEpochAt := refreshEpochAtMap st.kernel child },
               log := refreshDelegationReceipt actor child :: st.log }
  unfold refreshDelegationChainA
  unfold refreshDelegationStep at hexec
  by_cases hg : (stateAuthB st.kernel.caps actor child && (st.kernel.delegate child).isSome) = true
  · -- the kernel step committed: read off `k'` (frozen face) from `hexec`; the chained arm fires on the
    -- same gate AND adds the `delegationEpochAt` re-stamp (`refreshEpochAtMap`), which the residual injects.
    rw [if_pos hg] at hexec
    rw [if_pos (by simpa only [Bool.and_eq_true] using hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    -- the chained post: `delegations := refreshDelegationsMap …` AND `delegationEpochAt := refreshEpochAtMap …`,
    -- which is EXACTLY the frozen `k'` (delegations move) WITH the epoch stamp residual applied. Definitional.
    rfl
  · rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_refreshDelegationStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of refreshDelegation's OWN standalone full-state circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against refreshDelegation's GENUINE standalone descriptor `refreshDelegationE D hD` (the v2
`Surface2` circuit whose soundness is `refreshDelegationA_full_sound`), exactly as `BalanceA` welds against
`balanceAE`/`balanceA_full_sound`. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the
independent `refreshDelegation_iff_spec` (executor ⟺ `RefreshDelegationSpec`); the circuit side is the
audited `refreshDelegationA_full_sound` (circuit ⟹ `RefreshDelegationSpec`). Both name the SAME
`RefreshDelegationSpec`, so they PROVABLY agree on the WHOLE 17-field state + the log — a full-state weld. -/

/-- The Argus circuit interpretation of a `refreshDelegation` term: refreshDelegation's OWN audited
standalone v2 `Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (refreshDelegationE D
hD) (encodeE2 …)` satisfied on the encoded `(st, ⟨actor,child⟩, st')` triple (DEFINITIONALLY the
`EffectRefinement` hub's `effect2CircuitStep S (refreshDelegationE D hD) st ⟨actor,child⟩ st'`, inlined
here so this module imports only `Inst.refreshDelegationA`). Its soundness `refreshDelegationA_full_sound`
pins the complete `RefreshDelegationSpec`. The refreshDelegation-keyed analog of `balanceACircuit`, in the
descriptor universe where refresh carries its OWN genuine full-state circuit. -/
def refreshDelegationCircuit (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (st : RecChainedState) (actor child : CellId) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (refreshDelegationE D hD)
    (encodeE2 S (refreshDelegationE D hD) st { actor := actor, child := child } st')

/-- **`refreshDelegationSpec_unique` — the FROZEN-FACE spec pins a UNIQUE post-state.** Two chained states
that BOTH satisfy `RefreshDelegationSpec st actor child ·` are equal. `RefreshDelegationSpec` is a full-state
spec: it pins EVERY one of the 17 kernel fields + the log to `st`-determined values, so two satisfying
states agree field-by-field. (This is the deployed standalone descriptor's FROZEN face — `delegationEpochAt`
unchanged; the executor's freshness-restore stamp is the separate `RefreshDelegationFullSpec` named
residual.) Functionality WITHOUT routing through the now-strengthened executor iff. -/
theorem refreshDelegationSpec_unique {st st₁ st₂ : RecChainedState} {actor child : CellId}
    (h₁ : RefreshDelegationSpec st actor child st₁) (h₂ : RefreshDelegationSpec st actor child st₂) :
    st₁ = st₂ := by
  obtain ⟨_, d1, l1, a1, c1, p1, n1, r1, m1, b1, s1, f1, lc1, dc1, dl1, de1, dea1, h1'⟩ := h₁
  obtain ⟨_, d2, l2, a2, c2, p2, n2, r2, m2, b2, s2, f2, lc2, dc2, dl2, de2, dea2, h2'⟩ := h₂
  obtain ⟨k1, lg1⟩ := st₁; obtain ⟨k2, lg2⟩ := st₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := k1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := k2
  simp_all only []

/-- **`refreshDelegation_compile_sound` — the welded soundness (refreshDelegation slice), against
refreshDelegation's OWN full-state descriptor.**

Suppose, for the Argus refreshDelegation term `refreshDelegationStmt actor child`:
  * the standalone refreshDelegation circuit `refreshDelegationCircuit S D hD st actor child st'` (=
    `refreshDelegationE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-function digest portals (`hRest : RestIffNoDelegations S.RH`, `hLog :
    logHashInjective S.LH`, `hD : Function.Injective D`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (refreshDelegationStmt actor child) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the FROZEN-FACE chained post-state the IR term
produces: `st' = { kernel := k', log := refreshDelegationReceipt actor child :: st.log }`. I.e.
refreshDelegation's OWN standalone circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState
(`delegations child` overwritten with the parent snapshot, every other field FROZEN — including
`delegationEpochAt`, which BOTH the deployed circuit and the IR leave unchanged) AND the receipt log — the
full FROZEN `RefreshDelegationSpec`. (The FAITHFUL executor ADDS the freshness-restore epoch stamp; that is
the SEPARATE `RefreshDelegationFullSpec` named residual the deployed standalone descriptor does not yet
write-gate-force — `interp_refreshDelegationStmt_chained` carries it explicitly.) -/
theorem refreshDelegation_compile_sound
    (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (actor child : CellId) (k' : RecordKernelState)
    (hcirc : refreshDelegationCircuit S D hD st actor child st')
    (hexec : interp (refreshDelegationStmt actor child) st.kernel = some k') :
    st' = { kernel := k', log := refreshDelegationReceipt actor child :: st.log } := by
  -- circuit side: refreshDelegation's OWN audited soundness forces the FROZEN `RefreshDelegationSpec` on
  -- `(st, ⟨actor,child⟩, st')`.
  have hspec : RefreshDelegationSpec st actor child st' :=
    refreshDelegationA_full_sound S D hD hRest hLog st { actor := actor, child := child } st' hcirc
  -- IR side: the §2 cornerstone fixes `k'` to the FROZEN-FACE kernel step `refreshDelegationStep` post,
  -- which satisfies the SAME FROZEN `RefreshDelegationSpec` on `⟨k', receipt :: st.log⟩` (the `delegations`
  -- snapshot moved, every other field — `delegationEpochAt` included — frozen).
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep] at hexec
  unfold refreshDelegationStep at hexec
  by_cases hg : (stateAuthB st.kernel.caps actor child && (st.kernel.delegate child).isSome) = true
  · rw [if_pos hg] at hexec
    simp only [Option.some.injEq] at hexec
    have hgP : RefreshDelegationGuard st actor child := by
      simp only [RefreshDelegationGuard, Bool.and_eq_true] at hg ⊢; exact ⟨hg.1, hg.2⟩
    have hspec' : RefreshDelegationSpec st actor child
        { kernel := k', log := refreshDelegationReceipt actor child :: st.log } := by
      subst hexec
      exact ⟨hgP, by funext c; simp only [refreshDelegationsMap], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact refreshDelegationSpec_unique hspec hspec'
  · rw [if_neg hg] at hexec; exact absurd hexec (by simp)

#assert_axioms refreshDelegation_compile_sound

/-! ## §5 — NON-VACUITY: the IR term OVERWRITES the snapshot (observable), the gate REJECTS forged
inputs (fail-closed), and the reported kernel-vs-runtime divergence is a checked fact.

The cornerstone/weld would be hollow if refresh never committed, if the snapshot overwrite were a no-op, or
if the gate admitted everything. A concrete kernel `kRD` (child `1` has parent `0`, parent holds a
`node 7` cap, child `1` holds the self-authority cap over itself) exercises a real snapshot; the rejection
lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells `0`,`1` are live accounts; the PARENT cell `0` holds a
`node 7` cap (the c-list to be snapshotted) AND the self/over-`1` authority; the CHILD cell `1` has its
`delegate` pointer set to `some 0` and starts with an EMPTY `delegations` snapshot. The actor for the
refresh is cell `0` (which holds authority over `1` via its caps). -/
def kRD : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 7, Cap.node 0, Cap.node 1] else []
    delegate := fun c => if c = 1 then some 0 else none
    delegations := fun _ => [] }

/-- **NON-VACUITY (the SNAPSHOT is OBSERVABLE).** A committed refresh of child `1` OVERWRITES `1`'s
`delegations` snapshot from `[]` to the PARENT `0`'s current c-list `[node 7, node 0, node 1]` — the
`setDelegations`/`refreshDelegationsMap` overwrite is real (the parent c-list lands in the
child's snapshot, not a no-op). -/
theorem refreshDelegationStmt_snapshots :
    (interp (refreshDelegationStmt 0 1) kRD).map (fun k => k.delegations 1)
      = some [Cap.node 7, Cap.node 0, Cap.node 1] := by
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep]
  decide

/-- **NON-VACUITY (frame: a NON-child slot is untouched).** Refreshing child `1` leaves the parent `0`'s
own `delegations` slot verbatim (here empty) — the overwrite is LOCAL to the `child` slot
(`refreshDelegationsMap`'s off-`child` branch). The frame-respecting witness. -/
theorem refreshDelegationStmt_frames_other :
    (interp (refreshDelegationStmt 0 1) kRD).map (fun k => k.delegations 0) = some [] := by
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep]
  decide

/-- **NON-VACUITY (fail-closed: no parent).** A refresh of a cell with NO parent (`delegate child = none`
— here cell `0`, whose `delegate` is `none`) does NOT commit — the term returns `none` (the PARENT leg of
the gate fails, dregg1's `delegate.ok_or_else`). No snapshot is taken. -/
theorem refreshDelegationStmt_rejects_noParent :
    interp (refreshDelegationStmt 0 0) kRD = none := by
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A refresh attempted by a FOREIGN actor (cell `2`, which
holds NO cap over child `1` and is `≠ 1`, so it is NOT self-authorized) does NOT commit — the AUTHORITY leg
`stateAuthB 2 1` fails closed (`2 ≠ 1` and `caps 2 = []`), even though child `1` DOES have a parent. So the
refresh is SELF-only: a third party cannot refresh someone else's delegation. (A refresh by the
child itself, `actor = child = 1`, IS self-authorized — `stateAuthB` admits acting on one's own cell — so
the authority tooth must use a FOREIGN actor, which this witness does.) No snapshot is taken. -/
theorem refreshDelegationStmt_rejects_unauthorized :
    interp (refreshDelegationStmt 2 1) kRD = none := by
  rw [interp_refreshDelegationStmt_eq_refreshDelegationStep]
  decide

#assert_axioms refreshDelegationStmt_snapshots
#assert_axioms refreshDelegationStmt_frames_other
#assert_axioms refreshDelegationStmt_rejects_noParent
#assert_axioms refreshDelegationStmt_rejects_unauthorized

/-! ### §5.1 — THE REPORTED DIVERGENCE: the Lean kernel step UNDER-MODELS the Rust runtime's
`delegation_epoch` bump (the memory-flagged cap-refresh root-gap).

The full Rust runtime's `RefreshDelegation` does TWO things: (1) overwrite the child's `delegations`
snapshot with the parent's current c-list, AND (2) bump a `delegation_epoch` freshness counter. The Lean
kernel step `refreshDelegationStep` models ONLY (1). There is no `delegation_epoch` field on
`RecordKernelState` at all; the per-cell `delegate` (parent pointer) registry — the natural place a
monotone epoch witness would hang — is LEFT UNTOUCHED (frozen in `RefreshDelegationSpec`).

We pin (1) ⟹ (delegate frozen) as a DOCUMENTATION THEOREM so the under-model cannot silently regress: a
committed kernel refresh FREEZES `delegate` (the registry a faithful (2) would key its epoch off). This
makes the divergence a checked fact of the model, not a buried assumption. Closing it is a kernel-model
WIDENING (add a `delegationEpoch` registry + bump to `refreshDelegationStep`, then re-derive the
descriptor), explicitly OUT OF SCOPE for this weld. -/

/-- **`refreshKernel_undermodels_runtime_epoch` — the reported divergence, as a checked theorem.** A
committed kernel refresh FREEZES the per-cell `delegate` parent-pointer registry (it edits ONLY the
`delegations` snapshot): there is no `delegation_epoch` field on `RecordKernelState`, so the runtime's
freshness-counter bump is NOT modeled. This pins `delegate` frozen on commit, so the under-model is a
checked fact, not a buried assumption. -/
theorem refreshKernel_undermodels_runtime_epoch {k k' : RecordKernelState}
    {a : RefreshDelegationArgs} (h : refreshDelegationStep k a = some k') :
    k'.delegate = k.delegate := by
  unfold refreshDelegationStep at h
  by_cases hg : stateAuthB k.caps a.actor a.child && (k.delegate a.child).isSome
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`refreshKernel_freezes_delegate` — the under-model is OBSERVABLE (concrete witness).** After a
committed refresh of child `1` on `kRD`, the `delegate` parent pointer of `1` is STILL `some 0` (unchanged)
— there is no epoch/freshness state the kernel advanced beyond the `delegations` overwrite. So the verified
kernel post-state carries NO epoch witness the runtime would have bumped. The divergence is real, not a
labeling artifact. -/
theorem refreshKernel_freezes_delegate :
    (refreshDelegationStep kRD { actor := 0, child := 1 }).map (fun k => k.delegate 1) = some (some 0) := by
  decide

#assert_axioms refreshKernel_undermodels_runtime_epoch
#assert_axioms refreshKernel_freezes_delegate

end Dregg2.Circuit.Argus.Effects.RefreshDelegation
