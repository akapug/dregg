/-
# Dregg2.Authority.TemporalAlgebra — the TEMPORAL-MODAL layer of the guard algebra.

dregg1 carries ONE temporal guard — `StateConstraint::TemporalGate { not_before, not_after }`
(`turn/src/executor/mod.rs:252-257`; modeled as a witnessed seam at `CatalogInstances.lean:140`) —
and the polis amendment design leans on it as the COOLING-PERIOD primitive ("the amendment takes
effect only at a wave boundary strictly after its own finalization … re-derived as a TemporalGate",
`.docs-history-noclaude/CONSENSUS-FLEX.md §5`). But a single opaque window check is not an algebra: nothing states
that a window IS the meet of an `after` and a `before`, that cooling IS an `after` at the staged
height plus the period, that an opened vesting gate STAYS open on every future of the trace, or
that an expired window STAYS expired. This module supplies that algebra, as installable guard
ATOMS in the `RelCaveat`/`HeapAtom` shape (an inductive with a decidable, computable, FAIL-CLOSED
`eval`), composed beside the existing per-slot caveat gate the SAME way `RelationalCaveat.lean` and
`Substrate/HeapKernel.lean` composed theirs — and it WELDS the layer onto the proven CTL machinery
(`Proof/CTL.lean`, the Emerson–Clarke fixpoint calculus) so the modal claims ("once cooled, always
cooled") are SATISFACTION-SET theorems of the existing branching logic, not re-derived folklore.

## The clock (where height comes from)

The executor already threads a height: `Exec/Admission.lean`'s `AdmCtx.blockHeight` (dregg1's
`self.block_height`, preferred over `now` by `admissionClock`), and the receipt chain itself is a
clock — `RecChainedState.log.length` advances by EXACTLY one on every committed write
(`stateStep_factors`'s ChainLink/ObsAdvance conjuncts; `recordCell_obs_advances`). The atoms here
take the height as an explicit `Nat` argument — the SAME seam `AdmCtx` crosses — and
`committed_write_advances_clock` (§4) pins that the real executor's committed writes step the
abstract `heightClock` the CTL bridge is stated over: the height-indexed trace of the running
system IS a path of `heightClock`.

## Coordination cost (classified honestly, per `Authority/ConfluenceClassifier.lean`)

  * `afterHeight`/`beforeHeight`/`withinWindow`/`cooledSince` are **height-only** (the formal tooth
    is `eval_heightOnly_rec_irrel`): they read NOTHING but the clock. Any two nodes evaluating at
    the same height agree — coordination-FREE; and their admission sets are monotone (upward- or
    downward-closed) in the height, so they never flap.
  * `rateBound counterField k` reads ONE cell's committed PRE-state register (the `HeapAtom`
    cost class: one-cell read, no cross-cell view). BUT the *counting obligation* — that the
    register actually counts admissions — is program wiring (the counter slot must be bumped in
    the same turn, e.g. a `monotonicSeq` caveat on the counter slot), and a BOUND is not
    I-confluent: k concurrent in-window admissions each reading `count = k−1` would all admit, so
    enforcing "at most k per window" across concurrent proposers FORCES ordering through the
    target cell — the `ConfluenceClassifier` bounded-BREAKS pole. Within one tau-ordered cell
    history (where every admission is serialized through the cell) the register read is exact.
  * `challengeWindow challengeField stagedAt period` is the STAGED form of the evidence-object
    design (`.docs-history-noclaude/CONSENSUS-FLEX.md §7`): "admissible only if the window has elapsed AND no
    challenge object exists". Here the challenge presence is a one-cell REGISTER read
    (`challengeField ≠ 0` = a challenge was filed); the full form — the challenge object as a heap
    entry, refused via heap NON-membership (`Substrate/Heap.sorted_gap_excludes`) — rides the one
    rotation with the rest of the heap wire/circuit binding (`HeapKernel` header). Same one-cell
    cost class; the register IS where a filed challenge lands today.

## The CTL bridge (the lever: inherit, don't reinvent)

`heightClock` (Config := ℕ, Step := +1) is the height-indexed trace. The bridge theorems state
each pure-height atom's admission set AS a satisfaction set of the PROVEN fixpoint calculus:

  * `afterHeight_iff_AG` — `afterHeight h` admits at `ht` **iff** `ht ⊨ AG {h ≤ ·}`: an opened
    vesting gate is open on EVERY future of the trace (the gfp `AG`, via the proven
    `AG_iff_all_reachable`). "Once vested, vested forever."
  * `afterHeight_eventually_EF` — from ANY height, `ht ⊨ EF {afterHeight h admits}` (the lfp
    `EF`, via the proven `EF_iff_reachable`): every vesting gate eventually opens.
  * `beforeHeight_expiry_permanent_AG` — an EXPIRED `beforeHeight` is expired on every future:
    the complement is an `AG` invariant. "Deadlines don't reopen."
  * `cooledSince_iff_AG` — the polis cooling gate inherits the `AG` reading verbatim
    (it IS `afterHeight (stagedAt + period)`, `cooledSince_eq_afterHeight`).

Because these route through `AG_iff_all_reachable`/`EF_iff_reachable`, every CTL law already
proved (fixpoint unfoldings, monotonicity, duality, coinduction/induction rules) now applies to
the temporal guard layer with zero new model-checking machinery.

## TemporalGate becomes an INSTANCE (zero behavior change)

`temporalGate notBefore notAfter` is dregg1's gate shape, literally; `temporalGate_eq_withinWindow`
pins the two-sided gate to the `withinWindow` atom, `polisCooling_is_cooledSince` pins the polis
cooling gate (`not_before = stagedAt + Δ`, `not_after = none` — CONSENSUS-FLEX §5's staged
amendment) to the `cooledSince` atom, and `windowed_chain_is_withinWindow` pins the LIVE in-tree
height-window gate (the macaroon chain `CaveatChain.Demo.windowed`, executed on `execFullForestG`'s
`chainGateG` leg in `GatedForestCfg.lean §A4`) to the same atom — so the amendment machinery and
the live caveat-chain gate inherit the whole algebra as instances, with the SAME Bool semantics.

## The install (the `HeapAtom` composition pattern — no upstream file edited)

`temporalStateStepGuarded` runs the temporal-atom gate as a PRECONDITION (pre-state read, like
`caveatsAdmit`/`HeapAtom`), then the UNCHANGED `stateStepGuarded` (authority + membership +
lifecycle + per-slot caveats). A committed temporal write IS a committed `stateStepGuarded` write
(`temporalStateStepGuarded_eq`), so every existing keystone lifts verbatim (§FRAME); with an empty
atom list it IS the existing guarded write (`temporalStateStepGuarded_nil_eq`) — nothing regresses.

Pure; computable; `#guard`-witnessed both ways (vesting + auction). Every keystone
`#assert_axioms`-pinned to {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Exec.EffectsState
import Dregg2.Proof.CTL
import Dregg2.Authority.CaveatChain

namespace Dregg2.Authority.TemporalAlgebra

open Dregg2.Exec
open Dregg2.Exec.EffectsState
  (fieldOf stateAuthB stateStepGuarded stateStepGuarded_eq stateStep_factors
   guarded_state_conserves guarded_state_authGraph_unchanged
   guarded_state_authorized guarded_state_field_written)
open Dregg2.Execution (System Run Reachable)
open Dregg2.Proof.CTL (AG EF AG_iff_all_reachable EF_iff_reachable)
open Dregg2.Spec (execGraph)

/-! ## §1 — The modal atom family (the `RelCaveat`/`HeapAtom` shape). -/

/-- **The temporal guard atoms.** Each is a decidable, computable, FAIL-CLOSED admission check
against the turn context's height (and, for the two register atoms, the target cell's committed
PRE-state record — the `HeapAtom` one-cell cost class). -/
inductive TemporalAtom where
  /-- **`afterHeight h`** — admit iff `h ≤ height`. The VESTING / activation gate. Upward-closed:
  once open, open forever (`afterHeight_upward_closed`; CTL reading `afterHeight_iff_AG`). -/
  | afterHeight (h : Nat)
  /-- **`beforeHeight h`** — admit iff `height ≤ h`. The DEADLINE / expiry gate. Downward-closed;
  expiry is permanent (`beforeHeight_expiry_permanent_AG`). -/
  | beforeHeight (h : Nat)
  /-- **`withinWindow lo hi`** — admit iff `lo ≤ height ≤ hi`. dregg1's two-sided
  `TemporalGate { not_before, not_after }`; PROVABLY the meet `afterHeight lo ∧ beforeHeight hi`
  (`withinWindow_eq_after_and_before`). -/
  | withinWindow (lo hi : Nat)
  /-- **`cooledSince stagedAt period`** — admit iff `stagedAt + period ≤ height`: the staged
  object (amendment, recovery, parameter change) has COOLED for at least `period` since it was
  staged at `stagedAt`. THE polis cooling primitive (CONSENSUS-FLEX §5), generalized; refuses
  strictly inside the period (`cooledSince_refuses_inside`), admits at/after the boundary
  (`cooledSince_admits_after`), and is definitionally `afterHeight (stagedAt + period)`
  (`cooledSince_eq_afterHeight`) — so it inherits the vesting algebra wholesale. -/
  | cooledSince (stagedAt period : Nat)
  /-- **`rateBound counterField k`** — admit iff the target cell's committed admission COUNTER
  register reads `< k` (at most `k` admissions per window; the program resets/rotates the counter
  at window boundaries and bumps it on each admission — e.g. a `monotonicSeq` caveat on the
  counter slot). HONEST COST: a one-cell pre-state register read (the `HeapAtom` class), but the
  bound is NOT I-confluent — enforcing it across CONCURRENT proposers forces ordering through the
  target cell (the `ConfluenceClassifier` bounded-breaks pole); it is exact within the cell's
  tau-serialized history. -/
  | rateBound (counterField : FieldName) (k : Int)
  /-- **`challengeWindow challengeField stagedAt period`** — admit iff the challenge window has
  ELAPSED (`stagedAt + period ≤ height`) AND no challenge object exists (the challenge register
  reads `0`). The optimistic-execution gate that pairs with the evidence design (CONSENSUS-FLEX
  §7): anyone may file a challenge during the window (a write setting the register non-zero);
  settlement is admissible only after a challenge-free window. STAGED FORM: the register read
  stands in for heap non-membership of the challenge object — the heap form rides the one
  rotation (`Substrate/HeapKernel` header). -/
  | challengeWindow (challengeField : FieldName) (stagedAt period : Nat)
  deriving Repr, DecidableEq

/-- **`TemporalAtom.eval atom height rec`** — does the atom admit at clock `height`, with the
target cell's committed PRE-state record `rec` (read only by the two register atoms; absent/
ill-typed register ⇒ `0`, dregg1's `FIELD_ZERO`)? Decidable, computable, FAIL-CLOSED. -/
def TemporalAtom.eval : TemporalAtom → Nat → Value → Bool
  | .afterHeight h,                ht, _   => decide (h ≤ ht)
  | .beforeHeight h,               ht, _   => decide (ht ≤ h)
  | .withinWindow lo hi,           ht, _   => decide (lo ≤ ht) && decide (ht ≤ hi)
  | .cooledSince stagedAt period,  ht, _   => decide (stagedAt + period ≤ ht)
  | .rateBound counter k,          _,  rec => decide (fieldOf counter rec < k)
  | .challengeWindow ch staged p,  ht, rec =>
      decide (staged + p ≤ ht) && decide (fieldOf ch rec = 0)

/-- **`temporalAtomsAdmit atoms height rec`** — do ALL installed temporal atoms admit? FAIL-CLOSED
(one refusing atom rejects); the meet semantics every caveat surface shares
(`Token.admits`/`caveatsAdmit`/`relCaveatsAdmit`/`heapAtomsAdmit`). -/
def temporalAtomsAdmit (atoms : List TemporalAtom) (height : Nat) (rec : Value) : Bool :=
  atoms.all (fun a => a.eval height rec)

/-- The HEIGHT-ONLY classification: `true` exactly for the atoms that read nothing but the clock
(coordination-free; any node evaluating at the same height agrees). The two register atoms are
excluded — they carry the one-cell-read cost class. -/
def TemporalAtom.heightOnly : TemporalAtom → Bool
  | .afterHeight _      => true
  | .beforeHeight _     => true
  | .withinWindow _ _   => true
  | .cooledSince _ _    => true
  | .rateBound _ _      => false
  | .challengeWindow .. => false

/-- **The height-only class is formally record-blind** — its atoms' verdicts do not depend on the
record at all. The tooth behind the coordination-free classification: two evaluators that agree on
the height agree on the verdict, whatever state they hold. -/
theorem eval_heightOnly_rec_irrel (a : TemporalAtom) (ha : a.heightOnly = true)
    (ht : Nat) (rec rec' : Value) : a.eval ht rec = a.eval ht rec' := by
  cases a <;> simp_all [TemporalAtom.eval, TemporalAtom.heightOnly]

/-! ## §2 — The algebra: monotonicity, composition, cooling correctness. -/

/-- **`afterHeight` is UPWARD-CLOSED in the height** — once the vesting gate admits, it admits at
every later height. The order-theoretic core of "once vested, vested forever" (the branching-time
form is `afterHeight_iff_AG`). -/
theorem afterHeight_upward_closed {h ht ht' : Nat} (hle : ht ≤ ht') (rec rec' : Value)
    (hadm : (TemporalAtom.afterHeight h).eval ht rec = true) :
    (TemporalAtom.afterHeight h).eval ht' rec' = true := by
  simp only [TemporalAtom.eval, decide_eq_true_eq] at *; omega

/-- **`beforeHeight` is DOWNWARD-CLOSED in the height** — a deadline that admits now admitted at
every earlier height. Dually: once missed, missed forever (`beforeHeight_expiry_permanent_AG`). -/
theorem beforeHeight_downward_closed {h ht ht' : Nat} (hle : ht' ≤ ht) (rec rec' : Value)
    (hadm : (TemporalAtom.beforeHeight h).eval ht rec = true) :
    (TemporalAtom.beforeHeight h).eval ht' rec' = true := by
  simp only [TemporalAtom.eval, decide_eq_true_eq] at *; omega

/-- **COMPOSITION: a window IS the meet of an `after` and a `before`** —
`withinWindow lo hi = afterHeight lo ∧ beforeHeight hi`, definitionally. dregg1's two-sided
`TemporalGate` decomposes into the two monotone halves; every window law follows from the two
closure lemmas above. -/
theorem withinWindow_eq_after_and_before (lo hi ht : Nat) (rec : Value) :
    (TemporalAtom.withinWindow lo hi).eval ht rec
      = ((TemporalAtom.afterHeight lo).eval ht rec
          && (TemporalAtom.beforeHeight hi).eval ht rec) := rfl

/-- **`cooledSince` IS `afterHeight` at the staged height plus the period** — the cooling gate is
a vesting gate whose unlock height is computed from the staging. The whole `afterHeight` algebra
(upward closure, AG/EF readings) transfers along this equation. -/
theorem cooledSince_eq_afterHeight (stagedAt period ht : Nat) (rec : Value) :
    (TemporalAtom.cooledSince stagedAt period).eval ht rec
      = (TemporalAtom.afterHeight (stagedAt + period)).eval ht rec := rfl

/-- **COOLING CORRECTNESS (refusal half)** — strictly inside the cooling period the gate REFUSES:
no amendment takes effect before it has cooled. Fail-closed teeth for the polis machinery. -/
theorem cooledSince_refuses_inside {stagedAt period ht : Nat} (hin : ht < stagedAt + period)
    (rec : Value) : (TemporalAtom.cooledSince stagedAt period).eval ht rec = false := by
  simp only [TemporalAtom.eval, decide_eq_false_iff_not]; omega

/-- **COOLING CORRECTNESS (admission half)** — at or after the cooling boundary the gate ADMITS:
a cooled amendment is not blocked. Non-vacuous against the refusal half. -/
theorem cooledSince_admits_after {stagedAt period ht : Nat} (hc : stagedAt + period ≤ ht)
    (rec : Value) : (TemporalAtom.cooledSince stagedAt period).eval ht rec = true := by
  simp only [TemporalAtom.eval, decide_eq_true_eq]; omega

/-- **`cooledSince` is upward-closed** — once cooled, cooled at every later height (inherited from
`afterHeight_upward_closed` along `cooledSince_eq_afterHeight`). -/
theorem cooledSince_upward_closed {stagedAt period ht ht' : Nat} (hle : ht ≤ ht')
    (rec rec' : Value)
    (hadm : (TemporalAtom.cooledSince stagedAt period).eval ht rec = true) :
    (TemporalAtom.cooledSince stagedAt period).eval ht' rec' = true := by
  rw [cooledSince_eq_afterHeight] at *
  exact afterHeight_upward_closed hle rec rec' hadm

/-- **`challengeWindow` is upward-closed in the height AT A FIXED RECORD** — with the challenge
register unchanged, an elapsed challenge-free window stays elapsed. (NOT record-blind: a filed
challenge flips the verdict — that is the point of the atom.) -/
theorem challengeWindow_upward_closed_fixed_rec {ch : FieldName} {stagedAt period ht ht' : Nat}
    (hle : ht ≤ ht') (rec : Value)
    (hadm : (TemporalAtom.challengeWindow ch stagedAt period).eval ht rec = true) :
    (TemporalAtom.challengeWindow ch stagedAt period).eval ht' rec = true := by
  simp only [TemporalAtom.eval, Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨by omega, hadm.2⟩

/-! ## §3 — The INSTALL: the temporally-guarded field write (the `HeapAtom` composition pattern).

The temporal gate is a PRECONDITION (pre-state read, like `caveatsAdmit`): gate first, then the
UNCHANGED `stateStepGuarded` (authority + membership + lifecycle-liveness + per-slot caveats).
Fail-closed on either. The height crosses the same seam `AdmCtx.blockHeight` does. -/

/-- **`temporalStateStepGuarded s tAtoms height f actor target n` — the temporally-guarded field
write (computable).** First the temporal-atom gate (against the turn context's `height` and the
target's committed PRE-state record), then the existing caveat-gated write `stateStepGuarded`.
Commits EXACTLY `stateStepGuarded`'s post-state iff both gates pass — the temporal gate only
DECIDES, never mutates. -/
def temporalStateStepGuarded (s : RecChainedState) (tAtoms : List TemporalAtom) (height : Nat)
    (f : FieldName) (actor target : CellId) (n : Int) : Option RecChainedState :=
  if temporalAtomsAdmit tAtoms height (s.kernel.cell target) = true then
    stateStepGuarded s f actor target n
  else
    none

/-- **`temporalStateStepGuarded_eq`.** A committed temporally-guarded write IS the underlying
caveat-gated write (the temporal gate only restricts the domain). THE bridge that lifts every
existing `stateStepGuarded` keystone verbatim. -/
theorem temporalStateStepGuarded_eq {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    stateStepGuarded s f actor target n = some s' := by
  unfold temporalStateStepGuarded at h
  by_cases hg : temporalAtomsAdmit tAtoms height (s.kernel.cell target) = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`temporalStateStepGuarded_admits`.** A committed temporally-guarded write means EVERY
installed temporal atom admitted at the turn's height against the pre-state record — the witness
that the published temporal policy was enforced, not bypassed. -/
theorem temporalStateStepGuarded_admits {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    temporalAtomsAdmit tAtoms height (s.kernel.cell target) = true := by
  unfold temporalStateStepGuarded at h
  by_cases hg : temporalAtomsAdmit tAtoms height (s.kernel.cell target) = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`temporalStateStepGuarded_nil_eq` (the SUPERSET pin).** With NO temporal atoms installed the
temporally-guarded write IS the existing guarded write — nothing downstream regresses. -/
theorem temporalStateStepGuarded_nil_eq (s : RecChainedState) (height : Nat) (f : FieldName)
    (actor target : CellId) (n : Int) :
    temporalStateStepGuarded s [] height f actor target n = stateStepGuarded s f actor target n := by
  unfold temporalStateStepGuarded temporalAtomsAdmit
  simp [List.all_nil]

/-- **`temporalStateStepGuarded_violation_fails` (FAIL-CLOSED).** One refusing temporal atom ⇒ the
write does NOT commit: a not-yet-vested transfer, an expired bid, an uncooled amendment, an
over-rate admission, a challenged settlement — all rejected BY THE GUARDED WRITE. -/
theorem temporalStateStepGuarded_violation_fails (s : RecChainedState)
    (tAtoms : List TemporalAtom) (height : Nat) (f : FieldName) (actor target : CellId) (n : Int)
    (h : temporalAtomsAdmit tAtoms height (s.kernel.cell target) = false) :
    temporalStateStepGuarded s tAtoms height f actor target n = none := by
  unfold temporalStateStepGuarded
  rw [if_neg (by rw [h]; simp)]

/-! ### §3.FRAME — the existing keystones lift VERBATIM (instantiated, not re-proved). -/

/-- **BALANCE UNCHANGED** — a committed temporally-guarded write (of a non-`balance` field)
conserves the total balance: the temporal gate is balance-neutral. -/
theorem temporal_state_conserves {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int} (hf : f ≠ balanceField)
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  guarded_state_conserves hf (temporalStateStepGuarded_eq h)

/-- **AUTHORITY GRAPH UNCHANGED** — temporal gates decide writes, never connectivity. -/
theorem temporal_state_authGraph_unchanged {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  guarded_state_authGraph_unchanged (temporalStateStepGuarded_eq h)

/-- **AUTHORITY STILL REQUIRED** — the temporal gate sits ON TOP of the authority gate, never
instead of it: a committed temporal write was authorized. -/
theorem temporal_state_authorized {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  guarded_state_authorized (temporalStateStepGuarded_eq h)

/-- **THE FIELD IS WRITTEN** — a committed temporally-guarded write reads back the written value. -/
theorem temporal_state_field_written {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    fieldOf f (s'.kernel.cell target) = n :=
  guarded_state_field_written (temporalStateStepGuarded_eq h)

/-! ## §4 — The CTL BRIDGE: each pure-height atom's admission set is a satisfaction set of the
PROVEN branching calculus over the height-indexed trace. -/

/-- **`heightClock` — the height-indexed trace as a transition system.** Config = the chain
height, Step = the clock tick (`m = n + 1`). The committed-write projection of the running system:
`committed_write_advances_clock` shows every committed guarded write of the real executor steps
this clock. The CTL modalities (`Proof/CTL.lean`) over THIS system give the temporal atoms their
branching-time readings. -/
@[reducible] def heightClock : System where
  Config := Nat
  Step   := fun n m => m = n + 1

/-- A `heightClock` run only moves FORWARD: reachability implies `≤`. -/
theorem heightClock_run_le {n m : Nat} (h : Run heightClock n m) : n ≤ m := by
  have key : ∀ (a b : heightClock.Config), Run heightClock a b → a ≤ b := by
    intro a b hr
    induction hr with
    | refl s => exact Nat.le_refl s
    | @step s t u hst _ ih =>
        have hst' : t = s + 1 := hst
        subst hst'
        exact Nat.le_of_succ_le ih
  exact key n m h

/-- Every forward height is reached: `n ≤ m` implies a `heightClock` run from `n` to `m`. -/
theorem heightClock_run_of_le {n m : Nat} (h : n ≤ m) : Run heightClock n m := by
  induction h with
  | refl => exact Dregg2.Execution.Run.refl (S := heightClock) n
  | @step k _ ih =>
      exact ih.trans
        (Dregg2.Execution.Run.step (S := heightClock) (rfl : k + 1 = k + 1)
          (Dregg2.Execution.Run.refl (S := heightClock) (k + 1)))

/-- **`heightClock` reachability IS the order**: `Reachable heightClock n m ↔ n ≤ m`. The
height-indexed trace is the linear future of the clock. -/
theorem heightClock_reachable_iff (n m : Nat) : Reachable heightClock n m ↔ n ≤ m :=
  ⟨heightClock_run_le, heightClock_run_of_le⟩

/-- **THE EXECUTOR WELD** — a committed temporally-guarded write of the REAL executor steps
`heightClock` on the receipt-chain clock: `s.log.length ⟶ s'.log.length` is a clock tick (the
ChainLink/ObsAdvance conjunct of `stateStep_factors`, surfaced as a `heightClock.Step`). The
height-indexed trace the CTL bridge is stated over is the committed-write projection of the
running system, not a free-floating model. -/
theorem committed_write_advances_clock {s s' : RecChainedState} {tAtoms : List TemporalAtom}
    {height : Nat} {f : FieldName} {actor target : CellId} {n : Int}
    (h : temporalStateStepGuarded s tAtoms height f actor target n = some s') :
    heightClock.Step s.log.length s'.log.length := by
  have hfac := stateStep_factors (stateStepGuarded_eq (temporalStateStepGuarded_eq h))
  show s'.log.length = s.log.length + 1
  rw [hfac.2]
  simp

/-- **`afterHeight_iff_AG` — THE BRIDGE (globally shape).** The vesting atom admits at `ht` IFF
`ht` satisfies the branching invariant `AG {h ≤ ·}` on the height-indexed trace: an opened gate is
open on EVERY future. Routed through the PROVEN `AG_iff_all_reachable` (`Proof/CTL.lean §4`), so
the gfp calculus (unfolding, coinduction `AG_coind`, monotonicity, duality) applies to the vesting
gate's admission set with zero new machinery. "Once vested, vested forever" is a theorem of the
existing model-checking layer. -/
theorem afterHeight_iff_AG (h ht : Nat) (rec : Value) :
    (TemporalAtom.afterHeight h).eval ht rec = true
      ↔ ht ∈ AG heightClock { m | h ≤ m } := by
  rw [AG_iff_all_reachable]
  simp only [TemporalAtom.eval, decide_eq_true_eq, Set.mem_setOf_eq]
  constructor
  · intro hle t hreach
    exact Nat.le_trans hle (heightClock_run_le hreach)
  · intro hall
    exact hall ht
      (show Reachable heightClock ht ht from Dregg2.Execution.Run.refl (S := heightClock) ht)

/-- **`afterHeight_eventually_EF` (eventually shape).** From ANY height the vesting gate is
EVENTUALLY open: every `ht` satisfies `EF {afterHeight h admits}` on the height-indexed trace.
Routed through the PROVEN `EF_iff_reachable` — the lfp reachability calculus supplies the witness.
With `afterHeight_iff_AG`: the gate eventually opens, and once open never closes. -/
theorem afterHeight_eventually_EF (h ht : Nat) (rec : Value) :
    ht ∈ EF heightClock { m | (TemporalAtom.afterHeight h).eval m rec = true } := by
  rw [EF_iff_reachable]
  refine ⟨max ht h, heightClock_run_of_le (Nat.le_max_left _ _), ?_⟩
  simp only [Set.mem_setOf_eq, TemporalAtom.eval, decide_eq_true_eq]
  exact Nat.le_max_right _ _

/-- **`beforeHeight_expiry_permanent_AG`** — a MISSED deadline is missed on every future: the
expired set is an `AG` invariant of the height-indexed trace. "Deadlines don't reopen" — the dual
permanence to the vesting gate's. -/
theorem beforeHeight_expiry_permanent_AG (h ht : Nat) (rec : Value)
    (hexp : (TemporalAtom.beforeHeight h).eval ht rec = false) :
    ht ∈ AG heightClock { m | (TemporalAtom.beforeHeight h).eval m rec = false } := by
  rw [AG_iff_all_reachable]
  intro t hreach
  simp only [TemporalAtom.eval, decide_eq_false_iff_not, Set.mem_setOf_eq] at *
  have := heightClock_run_le hreach
  omega

/-- **`cooledSince_iff_AG`** — the polis cooling gate's branching reading, inherited verbatim:
the staged object is cooled at `ht` IFF `ht ⊨ AG {stagedAt + period ≤ ·}` — once an amendment has
cooled, it is cooled on EVERY future of the trace (no re-freezing). The amendment machinery's
permanence is a satisfaction-set theorem of the proven CTL layer. -/
theorem cooledSince_iff_AG (stagedAt period ht : Nat) (rec : Value) :
    (TemporalAtom.cooledSince stagedAt period).eval ht rec = true
      ↔ ht ∈ AG heightClock { m | stagedAt + period ≤ m } := by
  rw [cooledSince_eq_afterHeight]
  exact afterHeight_iff_AG (stagedAt + period) ht rec

/-! ## §5 — `TemporalGate` becomes an INSTANCE (zero behavior change).

dregg1's `StateConstraint::TemporalGate { not_before, not_after }` (`turn/src/executor/mod.rs:252`,
the witnessed seam at `CatalogInstances.lean:140`) is, semantically, a pair of monotone half-gates.
`temporalGate` is that shape literally; the theorems pin the polis cooling instance and the LIVE
in-tree window gate to the atoms, so both inherit the §2/§4 algebra with the SAME Bool verdicts. -/

/-- **`temporalGate notBefore notAfter`** — dregg1's gate shape, transcribed: an optional
`not_before` (compiled to `afterHeight`) and an optional `not_after` (compiled to `beforeHeight`).
`none` on either side = that half-gate absent (admits everything), exactly the Rust
`Option<u64>`. -/
def temporalGate (notBefore notAfter : Option Nat) : List TemporalAtom :=
  (notBefore.map TemporalAtom.afterHeight).toList
    ++ (notAfter.map TemporalAtom.beforeHeight).toList

/-- **The two-sided `TemporalGate` IS `withinWindow`** — same Bool verdict at every height. The
dregg1 gate is an instance of the atom family; the window algebra
(`withinWindow_eq_after_and_before` + the two closure laws) applies to it verbatim. -/
theorem temporalGate_eq_withinWindow (lo hi ht : Nat) (rec : Value) :
    temporalAtomsAdmit (temporalGate (some lo) (some hi)) ht rec
      = (TemporalAtom.withinWindow lo hi).eval ht rec := by
  simp [temporalGate, temporalAtomsAdmit, TemporalAtom.eval]

/-- **The polis amendment COOLING gate** — CONSENSUS-FLEX §5's staged amendment ("takes effect
only at a wave boundary strictly after its own finalization … re-derived as a TemporalGate"): a
`TemporalGate` whose `not_before` is the staging height plus the cooling period, `not_after`
absent. -/
def polisCooling (stagedAt period : Nat) : List TemporalAtom :=
  temporalGate (some (stagedAt + period)) none

/-- **THE POLIS COOLING GATE IS `cooledSince`** — same Bool verdict at every height and record:
the amendment machinery's cooling mechanism is an INSTANCE of the algebra (zero behavior change),
so it inherits cooling correctness (`cooledSince_refuses_inside`/`cooledSince_admits_after`),
upward closure, and the `AG` permanence reading (`cooledSince_iff_AG`) for free. -/
theorem polisCooling_is_cooledSince (stagedAt period ht : Nat) (rec : Value) :
    temporalAtomsAdmit (polisCooling stagedAt period) ht rec
      = (TemporalAtom.cooledSince stagedAt period).eval ht rec := by
  simp [polisCooling, temporalGate, temporalAtomsAdmit, TemporalAtom.eval]

/-- **The LIVE in-tree window gate is `withinWindow`** — the macaroon caveat chain
`CaveatChain.Demo.windowed` (height ≥ 100 then height ≤ 200; EXECUTED on `execFullForestG`'s
`chainGateG` leg, `GatedForestCfg.lean §A4`) has, link-for-link, the `withinWindow 100 200`
admission semantics. The live caveat-chain machinery inherits the temporal algebra as an
instance — no behavior change, the same Bool function. -/
theorem windowed_chain_is_withinWindow (ht : Nat) (rec : Value) :
    Dregg2.Authority.CaveatChain.Demo.windowed.admits ht Dregg2.Authority.CaveatChain.Demo.noD
      = (TemporalAtom.withinWindow 100 200).eval ht rec := by
  simp [Dregg2.Authority.CaveatChain.Demo.windowed, Dregg2.Authority.CaveatChain.Demo.root5,
        Dregg2.Authority.CaveatChain.seed, Dregg2.Authority.CaveatChain.Chain.append,
        Dregg2.Authority.CaveatChain.Chain.admits, Dregg2.Authority.Caveat.ok,
        TemporalAtom.eval]

/-! ## §6 — NON-VACUITY: every atom witnessed TRUE and FALSE; the vesting and auction examples
EXECUTED on the temporally-guarded write. -/

/-- A committed record carrying the two registers the register atoms read: an admission counter
at `3` and an empty challenge register. -/
def tRec : Value := .record [("bids_count", .int 3), ("challenge", .int 0)]

/-- The same record after a challenge was FILED (the challenge register is non-zero). -/
def tRecChallenged : Value := .record [("bids_count", .int 3), ("challenge", .int 1)]

-- afterHeight: TRUE at/after the boundary, FALSE before.
#guard (TemporalAtom.afterHeight 100).eval 150 tRec            --  true  (vested)
#guard (TemporalAtom.afterHeight 100).eval 50  tRec == false   --  false (still locked)
-- beforeHeight: TRUE before the deadline, FALSE after.
#guard (TemporalAtom.beforeHeight 200).eval 150 tRec           --  true  (in time)
#guard (TemporalAtom.beforeHeight 200).eval 250 tRec == false  --  false (expired)
-- withinWindow: TRUE inside, FALSE on both outsides.
#guard (TemporalAtom.withinWindow 10 20).eval 15 tRec          --  true  (in window)
#guard (TemporalAtom.withinWindow 10 20).eval 5  tRec == false --  false (too early)
#guard (TemporalAtom.withinWindow 10 20).eval 25 tRec == false --  false (too late)
-- cooledSince: FALSE strictly inside the period, TRUE at the boundary.
#guard (TemporalAtom.cooledSince 100 50).eval 149 tRec == false --  false (still cooling)
#guard (TemporalAtom.cooledSince 100 50).eval 150 tRec          --  true  (cooled)
-- rateBound: TRUE under the bound, FALSE at/over it (counter register reads 3).
#guard (TemporalAtom.rateBound "bids_count" 5).eval 0 tRec           --  true  (3 < 5)
#guard (TemporalAtom.rateBound "bids_count" 3).eval 0 tRec == false  --  false (3 ≮ 3)
-- challengeWindow: TRUE after a challenge-free window; FALSE while open; FALSE once challenged.
#guard (TemporalAtom.challengeWindow "challenge" 100 50).eval 150 tRec                     --  true
#guard (TemporalAtom.challengeWindow "challenge" 100 50).eval 120 tRec == false            --  false (window open)
#guard (TemporalAtom.challengeWindow "challenge" 100 50).eval 150 tRecChallenged == false  --  false (challenged)

/-- A chained state for the examples: cell 0 (owned by actor 0) carries a balance and the
auction/vesting slots; cell 1 is a bystander. Total balance 105. -/
def ssTemp : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("unlocked", .int 0),
                                                ("best_bid", .int 0), ("settled", .int 0)]
                         else .record [("balance", .int 5)]
        caps := fun _ => [] }
    log := [] }

/-! ### The VESTING example — the unlock write admitted ONLY `afterHeight 100`. -/

-- LOCKED: at height 50 the vesting write is REJECTED by the temporal gate (fail-closed).
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 100] 50 "unlocked" 0 0 1).isSome) == false
-- VESTED: at height 150 the SAME write COMMITS.
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 100] 150 "unlocked" 0 0 1).isSome)
-- The committed vesting write conserves balance and reads back (the lifted keystones, executed).
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 100] 150 "unlocked" 0 0 1).map
          (fun s => recTotal s.kernel)) == some 105
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 100] 150 "unlocked" 0 0 1).map
          (fun s => fieldOf "unlocked" (s.kernel.cell 0))) == some 1

/-! ### The AUCTION example — bids `withinWindow [10,20]`, settlement `afterHeight 21`. -/

-- BID in the window (height 15) COMMITS; too late (25) and too early (5) are REJECTED.
#guard ((temporalStateStepGuarded ssTemp [.withinWindow 10 20] 15 "best_bid" 0 0 7).isSome)
#guard ((temporalStateStepGuarded ssTemp [.withinWindow 10 20] 25 "best_bid" 0 0 7).isSome) == false
#guard ((temporalStateStepGuarded ssTemp [.withinWindow 10 20] 5  "best_bid" 0 0 7).isSome) == false
-- SETTLE after the window closes (25) COMMITS; settling DURING the bidding window is REJECTED.
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 21] 25 "settled" 0 0 1).isSome)
#guard ((temporalStateStepGuarded ssTemp [.afterHeight 21] 15 "settled" 0 0 1).isSome) == false

/-- **Non-vacuity at the theorem layer (refusal)** — the locked vesting write FAILS CLOSED via
`temporalStateStepGuarded_violation_fails`: the temporal gate rejected it, the write did not
commit. -/
example : temporalStateStepGuarded ssTemp [.afterHeight 100] 50 "unlocked" 0 0 1 = none :=
  temporalStateStepGuarded_violation_fails ssTemp [.afterHeight 100] 50 "unlocked" 0 0 1
    (by decide)

/-- **Non-vacuity at the theorem layer (admission witness)** — a committed vesting write carries
the proof that EVERY installed temporal atom admitted at the turn's height. -/
example (s' : RecChainedState)
    (h : temporalStateStepGuarded ssTemp [.afterHeight 100] 150 "unlocked" 0 0 1 = some s') :
    temporalAtomsAdmit [.afterHeight 100] 150 (ssTemp.kernel.cell 0) = true :=
  temporalStateStepGuarded_admits h

/-! ## §7 — Axiom-hygiene tripwires (every keystone pinned to the three kernel axioms). -/

#assert_axioms eval_heightOnly_rec_irrel
#assert_axioms afterHeight_upward_closed
#assert_axioms beforeHeight_downward_closed
#assert_axioms withinWindow_eq_after_and_before
#assert_axioms cooledSince_eq_afterHeight
#assert_axioms cooledSince_refuses_inside
#assert_axioms cooledSince_admits_after
#assert_axioms cooledSince_upward_closed
#assert_axioms challengeWindow_upward_closed_fixed_rec
#assert_axioms temporalStateStepGuarded_eq
#assert_axioms temporalStateStepGuarded_admits
#assert_axioms temporalStateStepGuarded_nil_eq
#assert_axioms temporalStateStepGuarded_violation_fails
#assert_axioms temporal_state_conserves
#assert_axioms temporal_state_authGraph_unchanged
#assert_axioms temporal_state_authorized
#assert_axioms temporal_state_field_written
#assert_axioms heightClock_run_le
#assert_axioms heightClock_run_of_le
#assert_axioms heightClock_reachable_iff
#assert_axioms committed_write_advances_clock
#assert_axioms afterHeight_iff_AG
#assert_axioms afterHeight_eventually_EF
#assert_axioms beforeHeight_expiry_permanent_AG
#assert_axioms cooledSince_iff_AG
#assert_axioms temporalGate_eq_withinWindow
#assert_axioms polisCooling_is_cooledSince
#assert_axioms windowed_chain_is_withinWindow

end Dregg2.Authority.TemporalAlgebra
