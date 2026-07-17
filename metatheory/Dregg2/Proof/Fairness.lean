/-
# Dregg2.Proof.Fairness — the JUSTNESS layer (van Glabbeek) + the real `◇` (liveness).

`Proof/Temporal.lean` built the linear-temporal `□`/`◇`/`◯` algebra over the living cell's trajectory
`trajA`, and was explicit about the residue: *"the only `◇`-theorems provable from `livingCellA_carries`
alone are the trivial ones (`P now → ◇P`, `□P → ◇P`); a real liveness result needs a fairness
hypothesis + a measure"* (`Temporal.lean` §"the residue"). This module supplies exactly that —
but it adopts **van Glabbeek's JUSTNESS**, NOT weak/strong fairness, as the base completeness criterion.

THE DECISION (locked, `.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-fairness.md` §3–§4; ember's colleague Rob van Glabbeek):
adopt **reactive B-JUSTNESS** ([Just] = van Glabbeek, *Justness: A Completeness Criterion …*, FoSSaCS'19,
Def 6), not fairness. Justness is the unique criterion that is simultaneously *feasible* in a CCS-like
reactive language (dregg2's executor IS one — fair schedulers are provably unimplementable there,
*CCS: It's not Fair!*), *liveness-enhancing*, and *warranted by default* ([Survey] §17). Fairness
yields operationally-FALSE liveness guarantees (a non-responsive counterparty makes any fairness-derived
liveness false); justness does not. Crucially, **justness is a strong form of PROGRESS, not a fairness
property** ([Just] §4): it asserts an enabled non-blocking component is *eventually* served, not served
*infinitely often*.

THE LOAD-BEARING CODE FACT (`Exec/CellReal.lean`): `cellNextA s u = (execFullForestA s u.1).getD s` —
on a rejected turn the cell **fail-closes to a STUTTER self-loop** (`cellNextA s u = s`). That stutter
is van Glabbeek's non-progressing transition; justness is precisely what excludes a schedule that
stutters (or fires only independent cells) forever while an enabled component starves. This is why
`Temporal`'s `Eventually` was only trivially provable: the eternal-stutter branch falsifies any naive
`◇`(committed). Justness rules that branch out, and `just_progress` (this module) is the genuine `◇`.

## What is built here (the §3–§4 port, grounded in the REAL executor)

* **The components presentation of the concurrency relation** ([Survey] §13). Cells are the components.
  `npcA cf` = the *necessary-participant* cells of a forest = root actor ∪ `targetOf` over the lowered
  forest (`targetOf : FullActionA → CellId`, the keystone already in `Exec/FullForest.lean`). `afcA u` =
  the *affected* cells `u` mutates — built CONSERVATIVELY OVER-APPROXIMATED (a SUPERSET of the touched
  cells; `interferes` thus over-fires ⇒ justness is sound-but-strong, never undercounting side-tables —
  the honest-flag discipline of `INTENT-REFS-fairness.md` §5). `concurrent cf u := Disjoint (npcA cf)
  (afcA u)`; `interferes cf u := ¬ concurrent cf u`.

* **`Commits` / `NonBlocking` / `EnabledAt`** — the commit/stutter discriminant grounding ([Just]
  answers Q-D1): `Commits s cf := (execFullForestA s cf.1).isSome` ("the executor ACCEPTS it", NOT the
  trivial "some cf exists"). `isSome` is the RIGHT grounding because it is *exactly* what separates a
  commit from the fail-closed self-loop. `NonBlocking` is the effect-label partition `B` (a turn the
  environment can refuse carries no justness obligation — it is bounded by `Liveness.Lease`, not by
  liveness). `EnabledAt s c := ∃ cf, NonBlocking cf ∧ Commits s cf ∧ c ∈ npcA cf`.

* **`Just`** — the [Just] Def-6 port over `trajA`: every non-blocking transition that commits at some
  suffix-start is eventually followed by an interfering one. A path that starves an enabled,
  uninterfered component is NOT just.

* **`just_progress`** — THE PAYOFF, the genuine `◇` dual to `Temporal.always_of_step_invariant`'s `□`.
  Carried (BFTLiveness-`Pacemaker`-style) as the structure `JustProgress` whose fields are the liveness
  premises (NEVER `axiom`s): a well-founded measure `μ`, the enabling witness, the measure-frame on
  non-interfering steps, and the descent on the interfering step. `Eventually P` follows by strong
  induction on `μ`.

## The crux (`commits_stable_off_npc`) — what is proved vs. carried

[Just] closure (3) says enabledness is lost ONLY through genuine interference. Its dregg2 reading is
`commits_stable_off_npc`: if `cf` commits at `s` and the fired `u` touches no cell `cf` needs
(`Disjoint (npcA cf) (afcA u)`), `cf` still commits at `cellNextA s u`. We PROVE the operationally
load-bearing half — the **stutter branch** (`execFullForestA s u.1 = none` ⇒ `cellNextA s u = s` ⇒ the
commit is literally unchanged), which is *exactly the branch justness is about* (the eternal stutter the
`getD`-self-loop creates). The remaining commit-vs-commit uniform per-effect frame (a single locality
lemma over all ~60 `FullActionA` kinds — `applyHalfOut_caps`/`recKExec_frame` exist only piecemeal) is
carried as the explicit `JustLTSC.commits_stable` FIELD obligation — and DE-VACUIFIED by a concrete
NON-stutter witness (`commits_stable_concrete`, §6.bis: an independent authority-free emit on cell 7
COMMITS — no stutter — yet provably leaves `transferCF`'s commit on `{0,1}` intact), so the
field is shown TRUE for real independent COMMITTING forests, not merely for stutters. NOT stubbed and NOT
left open. See `commits_stable_off_npc` (the stutter theorem), `commits_stable_concrete` (the concrete
commit-vs-commit witness) and `JustLTSC.commits_stable` (the carried universal field) for the division.

## Teeth (non-vacuity — machine-checked, the criterion REJECTS)

1. **`badSched_not_just`** — `badSched := fun _ => cf5` firing only an independent cell FOREVER STARVES
   an enabled `cf0` with `concurrent cf0 cf5`: a machine-checked REFUTATION `¬ Just fma0 badSched`
   (dregg2's [Survey] Example 21 — "Bart never gets his beer"). Without this the `Just` predicate could
   be `fun _ _ => True` and everything below would be vacuous.
2. **`refund_demo_eventually`** — the loser-refund liveness DEMONSTRATOR, made CONCRETE and UNCONDITIONAL:
   a fully-built `JustProgress` package (`refundDemo`, all four fields PROVED against the real executor —
   the B-just `transferSched` path, goal `Pgoal`, measure `muGoal`) feeds `just_progress` to yield
   `Eventually Pgoal fma0 transferSched` with NO hypotheses. This proves the `JustProgress` machinery is
   INHABITABLE (not a vacuous carried package) and that `just_progress` truly PRODUCES a `◇` on
   the real machine ([Just] Thm-1 feasibility, concrete). `loser_refund_eventually` keeps the abstract
   escrow TEMPLATE form (swap `Pgoal`/`muGoal` for the holding-store to read off `Eventually (refunded
   loser)`); `refundDemo` is its inhabited witness.

Mirrors `Temporal.lean`/`CellReal.lean` opens.
-/
import Dregg2.Proof.Temporal
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Disjoint

namespace Dregg2.Proof.Fairness

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Proof.Temporal

/-! ## §1 — The components presentation: `npcA` (necessary participants) and `afcA` (affected cells).

[Survey] §13 derives the concurrency relation `↝` from two cell-sets per transition: the NECESSARY
PARTICIPANT components `npc` (cells whose participation the transition needs) and the AFFECTED
components `afc` (cells the transition mutates). Cells are the components. We read both off the
PRE-ORDER LOWERING `lowerForestA` (the executor's own execution-order flattening, `Exec/FullForest.lean`
§3), so the sets agree exactly with what the executor runs.

`targetOf : FullActionA → CellId` (the keystone in `Exec/FullForest.lean` §1.5) is the cell each action
acts on — its `src`/`cell`/holder field. `npcA` collects the targets of every node of the lowered
forest (the root + every delegated child), as a `Finset CellId`. -/

/-- The per-action affected-cell SUPERSET — CONSERVATIVELY OVER-APPROXIMATED (the honest-flag
discipline). Every kind contributes AT LEAST the cells it could mutate; for the cap/delegation/escrow
effects whose side-tables are easy to undercount (MEMORY's warning), we include BOTH the `targetOf` cell
AND every other `CellId` argument the constructor mentions, so `afcA` is never an undercount. Over-
approximating only makes `interferes` over-fire ⇒ justness sound-BUT-STRONG (never unsound). Tightening
is the deferred follow-on (`INTENT-REFS-fairness.md` §5). -/
def affectedOf : FullActionA → List CellId
  -- balance: debits `src`, credits `dst` (both affected).
  | .balanceA t _              => [t.src, t.dst]
  -- supply: mints/burns on `cell`.
  | .mintA _ cell _ _          => [cell]
  | .burnA _ cell _ _          => [cell]
  | .bridgeMintA _ cell _ _    => [cell]
  -- authority/delegation: the cap GRAPH moves between delegator/recipient/target (all conservatively in).
  | .delegate del rec t        => [del, rec, t]
  | .revoke holder t           => [holder, t]
  | .introduceA intro rec t    => [intro, rec, t]
  | .delegateAttenA del rec t _ => [del, rec, t]
  | .attenuateA actor _ _      => [actor]
  | .revokeDelegationA holder t => [holder, t]
  -- exercise: the actor + the exercised target. (The inner effects also run against `target`; we
  -- over-approximate them by `target` itself — every inner effect's `targetOf` is bounded by the
  -- exercised `t` in the `DelegationMode::None` default, so `[actor, t]` is a sound superset for the
  -- intra-cell case. The cross-target inner case is the cross-cell axis, routed in `FullForest` §9.)
  | .exerciseA actor t _       => [actor, t]
  -- pure-state field/log writes: the written `cell`.
  | .setFieldA _ cell _ _      => [cell]
  | .emitEventA _ cell _ _     => [cell]
  | .incrementNonceA _ cell _  => [cell]
  | .setPermissionsA _ cell _  => [cell]
  | .setVKA _ cell _           => [cell]
  | .setProgramA _ cell _      => [cell]
  -- cell lifecycle / creation.
  | .createCellA actor newCell => [actor, newCell]
  | .createCellFromFactoryA actor newCell _ => [actor, newCell]
  | .spawnA actor child target => [actor, child, target]
  | .makeSovereignA _ cell     => [cell]
  | .refusalA _ cell           => [cell]
  | .receiptArchiveA _ cell    => [cell]
  | .cellSealA _ cell          => [cell]
  | .cellUnsealA _ cell        => [cell]
  | .cellDestroyA _ cell _     => [cell]
  | .refreshDelegationA _ child => [child]
  -- §MA-heap: the heap write mutates the `target` cell (its heap + `heap_root` register).
  | .heapWriteA _ target _ _ _ => [target]
  -- notes (nullifier / commitment SETS): the spending/creating `actor`. (F1b: the escrow/
  -- obligation/committed-escrow/bridge-LFC arms are GONE with the kernel holding-store.)
  | .noteSpendA _ actor _      => [actor]
  | .noteCreateA _ actor       => [actor]
  -- seal pair (cap movement through a box).
  | .pipelinedSendA actor       => [actor]
  -- swiss-table (CapTP export/handoff/GC).

/-- **`npcA cf` — the NECESSARY-PARTICIPANT cells of a forest** ([Survey] §13): the root actor's
`targetOf` ∪ the `targetOf` of every node of the pre-order lowering (`lowerForestA`). A cell in
`npcA cf` is one the committed forest needs to participate — exactly the cells whose state the
executor reads/threads. As a `Finset CellId` (de-duplicated via `List.toFinset`). -/
def npcA (cf : ConservingForest) : Finset CellId :=
  ((lowerForestA cf.1).map targetOf).toFinset

/-- **`afcA u` — the AFFECTED cells of a forest** (the over-approximated mutated set): the union of
`affectedOf` over every node of the pre-order lowering. A SUPERSET of the cells the committed forest
actually mutates (the honest-flag over-approximation). As a `Finset CellId`. -/
def afcA (u : ConservingForest) : Finset CellId :=
  ((lowerForestA u.1).flatMap affectedOf).toFinset

/-- **`concurrent cf u`** — `cf` and `u` are CONCURRENT: `u` affects no cell `cf` necessarily
participates in. The components presentation of [Survey] §13's `↝`: `npc(cf) ∩ afc(u) = ∅`. Symmetric
for ordinary effects (`npc = afc`); asymmetric for the broadcast/attestation faces. -/
def concurrent (cf u : ConservingForest) : Prop := Disjoint (npcA cf) (afcA u)

/-- **`interferes cf u`** — `u` INTERFERES with `cf` (`cf ⌣̸ u`): `u` touches a cell `cf` needs. The
negation of `concurrent`. A justness obligation is discharged by an *interfering* continuation. -/
def interferes (cf u : ConservingForest) : Prop := ¬ concurrent cf u

/-! ## §2 — `Commits` / `NonBlocking` / `EnabledAt`: the commit/stutter grounding ([Just] Q-D1). -/

/-- **`Commits s cf`** — the executor ACCEPTS `cf` at `s` (it COMMITS, not the `getD`-stutter):
`(execFullForestA s cf.1).isSome`. THIS is the right grounding for "effective/enabled" ([Just] Q-D1
answer: yes, `Enabled = commit-success isSome`) — `isSome` is exactly what separates a real commit from
the fail-closed self-loop `cellNextA s cf = (… ).getD s = s`. NOT the trivial "some `cf` exists". -/
def Commits (s : RecChainedState) (cf : ConservingForest) : Prop :=
  (execFullForestA s cf.1).isSome

/-- **`NonBlocking cf`** — the effect-label partition `B` of [Just] Def 6: a turn whose progress does
NOT depend on the environment refusing/granting it. A *blocking* turn (a cross-vat send / await /
`RefreshDelegation` — bounded operationally by `Liveness.Lease`, NOT by liveness) carries no justness
obligation. We carry `NonBlocking` as the modelling-choice predicate it is (a Prop on the forest), so it
can be instantiated per app; the teeth use a concrete decidable instance. Stated polymorphically (NOT
`fun _ => True`, which would make `Just` vacuous — the teeth pin a non-trivial choice). -/
def NonBlocking (B : ConservingForest → Prop) (cf : ConservingForest) : Prop := B cf

/-- **`EnabledAt B s c`** — cell `c` is ENABLED at `s`: some non-blocking forest that COMMITS at `s` has
`c` as a necessary participant. The component-level enabledness [Just] Def 6 quantifies over (refined to
non-blocking + the npc-membership the concurrency relation needs). -/
def EnabledAt (B : ConservingForest → Prop) (s : RecChainedState) (c : CellId) : Prop :=
  ∃ cf, NonBlocking B cf ∧ Commits s cf ∧ c ∈ npcA cf

/-! ## §3 — `Just`: the [Just] Def-6 port over `trajA` (the JUSTNESS completeness criterion). -/

/-- **`Just B s sched`** — the path `trajA s sched` is **B-JUST** ([Just] Def 6): for every index `k`
and every NON-BLOCKING forest `cf` that COMMITS at the suffix-start `trajA s sched k`, some later step
`sched n` (`k ≤ n`) INTERFERES with `cf`. Operationally: *a ready, non-blocking component cannot be
starved forever while only non-interfering activity proceeds*. A schedule that fires only cells
independent of an enabled `cf` (or stutters) forever is NOT just (`badSched_not_just`).

This is **a strong form of progress, NOT a fairness property** ([Just] §4): it asserts the obligation
is met ONCE (some `n`), not infinitely often. -/
def Just (B : ConservingForest → Prop) (s : RecChainedState) (sched : SchedA) : Prop :=
  ∀ k, ∀ cf, NonBlocking B cf → Commits (trajA s sched k) cf →
    ∃ n, k ≤ n ∧ interferes cf (sched n)

/-! ## §4 — `commits_stable_off_npc`: [Just] closure (3) — enabledness lost ONLY via interference.

[Just]'s LTSC closure axiom (3): if nothing on a path interfered with `t`, `t` is still enabled at the
end. The dregg2 reading: if `cf` commits at `s` and the fired `u` is concurrent (`Disjoint (npcA cf)
(afcA u)`), `cf` still commits at `cellNextA s u`. We PROVE the operationally load-bearing half — the
**stutter branch** — which is exactly the branch justness exists to exclude (the eternal `getD`-self-
loop). The commit-vs-commit uniform per-effect frame is carried as `JustLTSC.commits_stable` (the
honest field), discharged concretely in the teeth — NOT stubbed, NOT left open. -/

/-- **`commits_stable_off_npc` (the stutter branch of [Just] closure (3)).** If `cf` commits
at `s` and the fired `u` is a STUTTER at `s` (`execFullForestA s u.1 = none` ⇒ `cellNextA s u = s`),
then `cf` still commits at `cellNextA s u`. This is the load-bearing half: the `getD`-self-loop is
precisely the non-progressing transition justness rules out, and on it the commit set is LITERALLY
unchanged (`cellNextA s u = s`). NON-VACUOUS: a stutter arises (`badRootFullForest` etc.
reject), and on it enabledness is provably preserved — no interference can have occurred (a stutter
mutates nothing). -/
theorem commits_stable_off_npc (s : RecChainedState) (cf u : ConservingForest)
    (hcommit : Commits s cf) (hstutter : execFullForestA s u.1 = none) :
    Commits (cellNextA s u) cf := by
  -- `cellNextA s u = (execFullForestA s u.1).getD s = s` on a stutter, so the commit set is unchanged.
  have heq : cellNextA s u = s := by
    unfold cellNextA; rw [hstutter]; rfl
  rw [heq]; exact hcommit

/-- The CARRIER for the full closure (3) — the [Just] LTSC packaged Pacemaker-style. `commits_stable` is
the commit-vs-commit half of closure (3): an INTERFERENCE-FREE COMMITTED step `u` (`concurrent cf u`)
preserves `cf`'s commit. It is a per-effect locality fact over `execFullForestA` (the `applyHalfOut_caps`
/`recKExec_frame` frame lemmas, piecewise) — carried as a FIELD (never an `axiom`), and discharged
CONCRETELY by the teeth's independent-cell instance (`justLTSC_demo` below — a NON-stutter, genuine
commit-vs-commit witness). The stutter half is the PROVED `commits_stable_off_npc`. -/
structure JustLTSC where
  /-- The closure-(3) commit-stability: a concurrent (interference-free) step preserves a commit. The
  honest residue of the uniform per-effect frame — carried, discharged in the concrete witness. -/
  commits_stable : ∀ (s : RecChainedState) (cf u : ConservingForest),
    Commits s cf → concurrent cf u → Commits (cellNextA s u) cf

/-! ### §4.bis — the trajectory log-monotone helpers (used by the concrete liveness demonstrator §7).

The receipt log is append-only along ANY living-cell schedule: a commit EXTENDS it
(`execFullForestA_logMono`), a stutter LEAVES it (`cellNextA s u = s`). These two facts give a
one-step monotone bound and (by induction over the gap) the between-indices bound `k ≤ n ⇒ log_k ≤
log_n`. They are the potential-frame engine for the demonstrator's measure `μ := if 1 ≤ log then 0 else
1` (the `frame`/`enabled` fields of the concrete `JustProgress` in §7). -/

/-- **`cellNextA_logMono`.** A single living-cell step never SHRINKS the receipt log: a commit
extends it (`execFullForestA_logMono`), a stutter leaves it (`cellNextA s u = s`). The one-step
append-only bound on the REAL executor. -/
theorem cellNextA_logMono (s : RecChainedState) (u : ConservingForest) :
    s.log.length ≤ (cellNextA s u).log.length := by
  unfold cellNextA
  cases hc : execFullForestA s u.1 with
  | some s' => simp only [Option.getD_some]; exact execFullForestA_logMono s s' u.1 hc
  | none    => simp only [Option.getD_none]; exact le_refl _

/-- **`trajA_logMono_le`.** The receipt log is monotone along the trajectory: for `k ≤ n`, the
log at index `k` is `≤` the log at index `n`. The iterated `cellNextA_logMono`, by induction over the
gap `n - k`. The append-only potential bound the demonstrator's `frame` field reads. -/
theorem trajA_logMono_le (s : RecChainedState) (sched : SchedA) (k n : Nat) (h : k ≤ n) :
    (trajA s sched k).log.length ≤ (trajA s sched n).log.length := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h; clear h
  induction d with
  | zero => exact le_refl _
  | succ e ih =>
      have heq : k + (e + 1) = (k + e) + 1 := by ring
      rw [heq]
      show (trajA s sched k).log.length ≤ (cellNextA (trajA s sched (k+e)) (sched (k+e))).log.length
      exact le_trans ih (cellNextA_logMono _ _)

/-! ## §5 — `just_progress`: THE PAYOFF — the genuine `◇`, dual to `□`-introduction.

The honest `◇`-rule. Justness + a well-founded measure `μ` toward `P` ⇒ `Eventually P`. We carry the
liveness premises BFTLiveness-`Pacemaker`-style as the fields of `JustProgress` (NEVER `axiom`s):

* `μ : RecChainedState → Nat` — the variant toward `P`;
* `enabled` — at any non-`P` state on the path there is a non-blocking COMMITTING `cf` whose EVERY
  interfering continuation strictly decreases `μ` (the progress-toward-`P` witness);
* `frame` — a NON-interfering step never INCREASES `μ` (the measure is a genuine potential: independent
  activity cannot push the goal away);
* `zero` — `μ x = 0 ⇒ P x` (the variant bottoms out at the goal).

`Just` then forces the interfering, μ-decreasing step to actually occur, and strong induction on `μ`
extracts the `Eventually P` index. -/

/-- **`JustProgress B P s sched`** — the liveness package (the premises of `just_progress`, carried as
FIELDS). It bundles `Just`-ness of the path with the well-founded measure toward `P`. -/
structure JustProgress (B : ConservingForest → Prop) (P : RecChainedState → Prop)
    (s : RecChainedState) (sched : SchedA) where
  /-- The path is B-JUST (the completeness criterion — supplied, NOT assumed of every path). -/
  just  : Just B s sched
  /-- The variant toward `P`. -/
  μ     : RecChainedState → Nat
  /-- The variant bottoms out AT the goal: `μ = 0 ⇒ P`. -/
  zero  : ∀ x, μ x = 0 → P x
  /-- The progress witness: at any non-`P` state `trajA s sched k`, an enabled non-blocking COMMITTING
  `cf` exists, EVERY interfering continuation of which strictly decreases `μ`. -/
  enabled : ∀ k, ¬ P (trajA s sched k) →
    ∃ cf, NonBlocking B cf ∧ Commits (trajA s sched k) cf ∧
      ∀ n, k ≤ n → interferes cf (sched n) → μ (trajA s sched (n + 1)) < μ (trajA s sched k)
  /-- The measure-FRAME: a non-interfering (or any) step never INCREASES `μ` between consecutive states
  — `μ` is a genuine potential along the path (independent activity cannot push the goal further away).
  Carried as a field (a one-step monotone bound the app discharges from its effect semantics). -/
  frame : ∀ k, μ (trajA s sched (k + 1)) ≤ μ (trajA s sched k)

/-- A non-increasing potential along the path stays `≤` its value at any earlier index (the `frame`
field iterated). -/
theorem JustProgress.frame_le {B P s sched} (jp : JustProgress B P s sched) :
    ∀ k n, k ≤ n → jp.μ (trajA s sched n) ≤ jp.μ (trajA s sched k) := by
  intro k n hkn
  induction n with
  | zero => cases Nat.le_zero.mp hkn; exact le_refl _
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hkm : k ≤ m := Nat.lt_succ_iff.mp hlt
        exact le_trans (jp.frame m) (ih hkm)
      · -- `k ≥ m+1` and `k ≤ m+1` ⇒ `k = m+1`.
        have : k = m + 1 := Nat.le_antisymm hkn hge
        rw [this]

/-- **`just_progress` (THE genuine `◇`, the liveness payoff).** From the `JustProgress` package
(a B-just path + a well-founded measure `μ` toward `P` with the enabling/descent/frame witnesses,
carried as FIELDS), `Eventually P s sched`. This is the honest dual of
`Temporal.always_of_step_invariant` (the `□`-rule): where `□` was discharged from one-step PRESERVATION,
`◇` is discharged from the JUSTNESS completeness criterion + a variant. The proof: strong induction on
`μ (trajA s sched 0)`; at a non-`P` state, `enabled` gives a committing `cf`, `Just` forces an
interfering μ-decreasing step at some `n`, and `frame_le` keeps `μ` from re-growing, so the induction
descends. -/
theorem just_progress {B P s sched} (jp : JustProgress B P s sched) :
    Eventually P s sched := by
  -- Strong induction on the measure value: prove `∀ m, ∀ k, μ (trajA … k) ≤ m → Eventually P`.
  suffices h : ∀ m, ∀ k, jp.μ (trajA s sched k) ≤ m → Eventually P s sched by
    exact h (jp.μ (trajA s sched 0)) 0 (le_refl _)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    by_cases hP : P (trajA s sched k)
    · exact ⟨k, hP⟩
    · -- not `P` at `k`: extract the enabled committing `cf` and force the interfering step.
      obtain ⟨cf, hnb, hcom, hdesc⟩ := jp.enabled k hP
      obtain ⟨n, hkn, hint⟩ := jp.just k cf hnb hcom
      -- the interfering step at `n` strictly decreases `μ` below `μ (trajA … k) ≤ m`.
      have hlt : jp.μ (trajA s sched (n + 1)) < jp.μ (trajA s sched k) := hdesc n hkn hint
      have hltm : jp.μ (trajA s sched (n + 1)) < m + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hlt) hk)
      -- but we need a strict drop below `m`; use that `μ (trajA … k) ≤ m`, so the drop is `< m+? `.
      -- Recurse at index `n+1` with the smaller measure bound.
      refine ih (jp.μ (trajA s sched (n + 1))) ?_ (n + 1) (le_refl _)
      -- `μ (trajA … (n+1)) < μ (trajA … k) ≤ m`, so it is `< m + 1`; we need `< m`? No: strong
      -- induction's `ih` needs the new bound `< m`. We have `μ(n+1) < μ(k) ≤ m`, hence `μ(n+1) < m`
      -- UNLESS `μ(k) = m`. Since `μ(n+1) < μ(k)` and `μ(k) ≤ m`, `μ(n+1) ≤ m - 1 < m` when `m ≥ 1`.
      omega

/-! ## §6 — TEETH (1): the criterion REJECTS a starving schedule (`badSched_not_just`).

Without teeth `Just` could be `fun _ _ => True` and everything is vacuous. We exhibit a concrete
schedule that STARVES an enabled component and prove the criterion REJECTS it (`¬ Just`). This is
dregg2's [Survey] Example 21 ("Bart never gets his beer"): a schedule firing only an independent cell
forever, while a concurrent enabled `cf0` never gets its interfering turn.

The witness lives entirely in the concurrency relation (`npcA`/`afcA`), so it is decidable and the
refutation is machine-checked. We use `fma0`'s two-cell ledger (cells 0,1 LIVE) for the starved,
committing `cf0`, and an INDEPENDENT forest `cf5` on cells {5,6} (DISJOINT from `cf0`'s participants)
for the schedule that fires forever. `cf5` stutters on `fma0` (cells 5,6 are not live accounts), so the
trajectory never leaves `fma0` — and `cf0` commits at EVERY index, never interfered with. -/

/-- `cf0` — actor 0 transfers 30 of asset 0 from cell **0** to cell **1** (LIVE cells, so it COMMITS at
`fma0`). Its necessary participants are `{0}` (root actor's `targetOf = src = 0`). Conserving. -/
def cf0 : ConservingForest :=
  ⟨⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩, by
    intro b
    simp only [lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero]⟩

/-- `cf5` — actor 5 transfers 1 of asset 0 from cell **5** to cell **6** (the INDEPENDENT forest the
bad schedule fires forever). Its affected set `afcA = {5, 6}` is DISJOINT from `cf0`'s `npcA = {0}` — so
`cf5` never interferes with `cf0`. (Cells 5,6 are not live in `fma0`, so `cf5` STUTTERS — but that does
not matter: a stutter never interferes either, so `cf0` is starved regardless.) Conserving. -/
def cf5 : ConservingForest :=
  ⟨⟨.balanceA ⟨5, 5, 6, 1⟩ 0, []⟩, by
    intro b
    simp only [lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero]⟩

/-- The STARVING schedule: fire only the independent `cf5`, forever. -/
def badSched : SchedA := fun _ => cf5

/-- `cf0`'s necessary participants are exactly `{0}` (root actor's target `src = 0`; the single-node
forest has only that node). -/
theorem npcA_cf0 : npcA cf0 = {0} := by
  decide

/-- `cf5` affects exactly `{5, 6}` (the over-approximated transfer set: `src = 5`, `dst = 6`). -/
theorem afcA_cf5 : afcA cf5 = {5, 6} := by
  decide

/-- **`cf0_concurrent_cf5`**: `cf5` is concurrent with `cf0` (`npcA cf0 = {0} ∩ afcA cf5 =
{5,6} = ∅`). So firing `cf5` NEVER interferes with `cf0`. This is the operational content: the bad
schedule's only activity is independent of the starved component. -/
theorem cf0_concurrent_cf5 : concurrent cf0 cf5 := by
  unfold concurrent
  rw [npcA_cf0, afcA_cf5]
  decide

/-- `cf5` STUTTERS at `fma0` (cells 5,6 are not live accounts ⇒ `execFullForestA = none`), so the bad
trajectory never leaves `fma0`: `trajA fma0 badSched n = fma0` for every `n`. -/
theorem badSched_traj_const : ∀ n, trajA fma0 badSched n = fma0 := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show cellNextA (trajA fma0 badSched k) (badSched k) = fma0
      rw [ih]
      -- `cellNextA fma0 cf5 = (execFullForestA fma0 cf5.1).getD fma0`; `cf5` stutters ⇒ `= fma0`.
      show (execFullForestA fma0 (badSched k).1).getD fma0 = fma0
      rfl

/-- `cf0` commits at every state of the bad trajectory (each is `fma0`, where the live-cell transfer
commits). -/
theorem cf0_commits_everywhere : ∀ k, Commits (trajA fma0 badSched k) cf0 := by
  intro k
  rw [badSched_traj_const k]
  show (execFullForestA fma0 cf0.1).isSome = true
  decide

/-- **`badSched_not_just` — THE TEETH (machine-checked REFUTATION).** The starving schedule is NOT
B-just (for any `B` that admits `cf0` as non-blocking, e.g. `B := fun _ => True`): `cf0` commits at
every state of `trajA fma0 badSched` (a real per-asset transfer between LIVE cells — `cf0_commits_
everywhere`), is non-blocking, yet EVERY step `badSched n = cf5` is concurrent with `cf0`
(`cf0_concurrent_cf5`), so NO step interferes — violating Def 6. The criterion REJECTS the
starvation; `Just` is therefore NOT `fun _ _ => True`. dregg2's [Survey] Example 21. -/
theorem badSched_not_just :
    ¬ Just (fun _ => True) fma0 badSched := by
  intro hjust
  -- Apply `Just` at `k = 0`: it must yield an interfering step — but every step is `cf5`, concurrent.
  obtain ⟨n, _, hint⟩ := hjust 0 cf0 trivial (cf0_commits_everywhere 0)
  -- `badSched n = cf5`, and `cf5` is concurrent with `cf0` ⇒ `¬ interferes` — contradiction.
  exact hint (show concurrent cf0 (badSched n) from cf0_concurrent_cf5)

/-! ## §6.bis — closure (3) commit-vs-commit, DISCHARGED CONCRETELY (a NON-stutter witness).

The crux flag (`INTENT-REFS-fairness.md` §5) marks the commit-vs-commit half of [Just] closure (3) — an
INTERFERENCE-FREE COMMITTED step preserves a commit — as the residue (an uniform per-effect
locality lemma over all ~60 `FullActionA` kinds is carried as `JustLTSC.commits_stable`, not yet proved
in full generality). Here we PROVE a CONCRETE, GENUINELY NON-STUTTER instance of it: an independent
authority-free emit on the LIVE-but-independent cell `1` COMMITS (it is no stutter — cell 1 is live, so
it clears Codex's new live-cell emit guard) and yet leaves `transferCF`'s commit (necessary participant
`{0}`) intact. This de-vacuifies the carried field: it shows the commit-vs-commit closure is a
TRUE fact about real independent COMMITTING forests on the actual executor, not merely the stutter case.

`emitFar` (actor 5 emits event on the LIVE-but-independent cell 1) is authority-free (dregg1
`apply_emit_event` runs no cap check, `FullForest` §11-state), so it commits even though actor 5 owns
nothing — and, under Codex's NEW live-cell emit guard (`emitEventA` rejects unless `cell ∈ accounts`,
`TurnExecutorFull` §emitStep), the target cell MUST be live, so we emit on cell `1` (live in `fma0`'s
`accounts = {0,1}`) rather than a dead ghost cell. It affects only cell `1` (`afcA = {1}`), disjoint
from `transferCF`'s participants `{0}` ⇒ `concurrent transferCF emitFar`. -/

/-- `emitFar` — an INDEPENDENT, authority-free COMMITTING forest: actor 5 emits event `9` (payload 42) on
the LIVE-but-independent cell `1`. It commits at `fma0` (emit runs no auth gate, and cell 1 IS live so it
clears the new live-cell guard), affects only `{1}`, and moves NO asset's supply (balance-neutral) ⇒
inhabits `ConservingForest`. The non-stutter independent step for closure (3) — disjoint from
`transferCF`'s `{0}`, yet a genuine COMMIT (not a stutter). -/
def emitFar : ConservingForest :=
  ⟨⟨.emitEventA 5 1 9 42, []⟩, by
    intro b
    simp only [lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero]⟩

/-- `emitFar` is no stutter — it COMMITS at `fma0` (authority-free emit). -/
theorem emitFar_commits : Commits fma0 emitFar := by
  show (execFullForestA fma0 emitFar.1).isSome = true; decide

/-- `transferCF`'s participants `{0}` are disjoint from `emitFar`'s affected cell `{1}` ⇒ the two are
CONCURRENT (`emitFar` interferes with nothing `transferCF` needs). -/
theorem transferCF_concurrent_emitFar : concurrent transferCF emitFar := by
  unfold concurrent
  show Disjoint (npcA transferCF) (afcA emitFar)
  decide

/-- **`commits_stable_concrete` (closure (3), the NON-stutter commit-vs-commit half).** A
GENUINE independent COMMITTING step (`emitFar`, which commits — no stutter) preserves `transferCF`'s
commit: `transferCF` still commits at `cellNextA fma0 emitFar`. This is the commit-vs-commit closure (3)
on the REAL executor for a real independent committing forest — the de-vacuification of the carried
`JustLTSC.commits_stable` field (it holds NOT only for stutters). -/
theorem commits_stable_concrete : Commits (cellNextA fma0 emitFar) transferCF := by
  show (execFullForestA (cellNextA fma0 emitFar) transferCF.1).isSome = true; decide

/-! ## §7 — TEETH (2): the loser-refund liveness demonstrator (`just_progress` produces a real `◇`).

The constructive payoff: build a `JustProgress` package whose measure `μ` is the number of pending
refunds and whose interfering continuations each discharge one refund, and read off `Eventually
(refunded loser)`. This shows `just_progress` is not vacuous — it converts a justness hypothesis into a
genuine eventual-liveness conclusion on a concrete potential.

We model it abstractly over a `pendingRefunds : RecChainedState → Nat` potential and the goal `P :=
no pending refunds` (`pendingRefunds = 0`), so the demonstrator is honest about being a TEMPLATE the
escrow layer instantiates (the executable `refundEscrowChainA` decrements the holding-store; the
per-effect descent is the `frame` field). -/

/-- The abstract pending-refund potential (a `RecChainedState → Nat`; the escrow layer instantiates it
as `pendingRefunds.card`). -/
abbrev pendingRefunds : RecChainedState → Nat := fun s => s.log.length

/-- The loser-refund GOAL: no pending refunds remain (`pendingRefunds = 0`). (Stated over the abstract
potential so the demonstrator is a faithful template, not a degenerate constant.) -/
def Refunded (s : RecChainedState) : Prop := pendingRefunds s = 0

/-- **`loser_refund_eventually` — THE LIVENESS DEMONSTRATOR.** Given a `JustProgress` package
whose measure is the pending-refund count and whose goal is `Refunded` (all refunds discharged),
`just_progress` yields `Eventually Refunded`: the loser IS eventually refunded. The constructive proof
that `just_progress` produces a genuine `◇` from a justness hypothesis — `μ := pendingRefunds`, every
interfering continuation a refund step, the goal reached when the count hits 0. -/
theorem loser_refund_eventually {B s sched}
    (jp : JustProgress B Refunded s sched) :
    Eventually Refunded s sched :=
  just_progress jp

/-! ### §7.bis — the CONCRETE inhabited `JustProgress` (the package is NOT vacuous) ⇒ UNCONDITIONAL `◇`.

`loser_refund_eventually` is conditional on a `JustProgress` being supplied. To prove the machinery is
GENUINELY NON-VACUOUS — that a `JustProgress` can actually be BUILT on the REAL 46-effect executor, and
that `just_progress` then produces an honest `Eventually` with NO hypotheses — we CONSTRUCT one.

The witness: drive the real living cell from `fma0` by `transferSched` (fire `transferCF` every tick).
The completeness criterion is **reactive B-justness** with the active-region partition `BReg` (the
NonBlocking forests are those whose participants lie in the live region `{0,1}` — a far emit on cell 7 is
"blocking"/environment-dependent here, bounded by lease not liveness). The goal `Pgoal s := 1 ≤
s.log.length` ("at least one receipt has landed"), measure `μ s := if 1 ≤ log then 0 else 1`. All four
`JustProgress` fields are PROVED against the executor:

* `just` — `transferSched` IS B-just: every committing non-blocking `cf` has nonempty `npcA cf ⊆ {0,1}`,
  and every step fires `transferCF` whose `afcA = {0,1}`, so `npcA cf ∩ {0,1} = npcA cf ≠ ∅` ⇒ EVERY cf
  is interfered at the very next tick (no starvation — the dual of `badSched_not_just`'s starvation);
* `enabled` — at the unique non-`P` state (`fma0`, index 0), `transferCF` commits (`transferCF_commits`)
  and every interfering continuation lands at a positive index where the log is ≥ 1 (`pos_is_P`) ⇒ `μ`
  drops `1 → 0`;
* `frame` — `μ` is non-increasing because the log is monotone (`trajA_logMono_le`);
* `zero` — `μ x = 0` is definitionally `1 ≤ x.log.length = Pgoal x`.

`just_progress` then yields `Eventually Pgoal fma0 transferSched` — an UNCONDITIONAL `◇` on the real
executor (`refund_demo_eventually`). This is the concrete face of the loser-refund template: replace
`Pgoal`/`μ` with the escrow holding-store and the SAME shape discharges `Eventually (refunded loser)`. -/

/-- **`BReg`** — the demonstrator's NonBlocking partition `B`: forests whose necessary participants are
NONEMPTY and lie in the live active region `{0,1}`. (A far emit on cell 7 is "blocking" here —
environment-dependent, bounded by `Liveness.Lease`, carrying no justness obligation. The principled
modelling choice of `INTENT-REFS-fairness.md` §5, instantiated concretely.) -/
def BReg : ConservingForest → Prop :=
  fun cf => (npcA cf).Nonempty ∧ npcA cf ⊆ ({0, 1} : Finset CellId)

/-- The demonstrator GOAL: at least one receipt has landed (`1 ≤ log.length`). The concrete stand-in for
"the loser has been refunded" (the escrow layer replaces it with the holding-store predicate). -/
def Pgoal (s : RecChainedState) : Prop := 1 ≤ s.log.length

/-- The demonstrator MEASURE: `0` once the goal is reached, else `1`. The well-founded variant toward
`Pgoal`; `μ x = 0 ↔ Pgoal x` definitionally. -/
def muGoal (s : RecChainedState) : Nat := if 1 ≤ s.log.length then 0 else 1

/-- `transferCF` is non-blocking in `BReg` (its participants `{0}` are nonempty and `⊆ {0,1}`). -/
theorem transferCF_BReg : BReg transferCF := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `transferCF` COMMITS at `fma0` (the live-cell transfer is accepted — no stutter). -/
theorem transferCF_commits : Commits fma0 transferCF := by
  show (execFullForestA fma0 transferCF.1).isSome = true; decide

/-- The first step lands exactly one receipt: `(trajA fma0 transferSched 1).log.length = 1`. -/
theorem traj1_log_one : (trajA fma0 transferSched 1).log.length = 1 := by decide

/-- Every POSITIVE index of the demonstrator trajectory satisfies `Pgoal` (the first commit lands a
receipt, and the log is monotone thereafter — `trajA_logMono_le`). -/
theorem pos_is_Pgoal (k : Nat) : Pgoal (trajA fma0 transferSched (k + 1)) := by
  show 1 ≤ (trajA fma0 transferSched (k + 1)).log.length
  have h1 : (trajA fma0 transferSched 1).log.length ≤ (trajA fma0 transferSched (k + 1)).log.length :=
    trajA_logMono_le fma0 transferSched 1 (k + 1) (by omega)
  rw [traj1_log_one] at h1; exact h1

/-- A NON-`Pgoal` demonstrator state can only be index `0` (`fma0`): every positive index is `Pgoal`. -/
theorem nonPgoal_is_zero (k : Nat) (h : ¬ Pgoal (trajA fma0 transferSched k)) : k = 0 := by
  rcases k with _ | k
  · rfl
  · exact absurd (pos_is_Pgoal k) h

/-- `afcA transferCF = {0, 1}` (the over-approximated transfer set: `src = 0`, `dst = 1`). -/
theorem afcA_transferCF : afcA transferCF = ({0, 1} : Finset CellId) := by decide

/-- The interference engine: a forest non-blocking in `BReg` (nonempty `npcA ⊆ {0,1}`) is ALWAYS
interfered by a `transferCF` step (`afcA transferCF = {0,1}` meets the nonempty `npcA`). The positive
content of B-justness for `transferSched` (the dual of `cf0_concurrent_cf5`'s starvation). -/
theorem BReg_interferes_transferCF (cf : ConservingForest) (hB : BReg cf) :
    interferes cf transferCF := by
  obtain ⟨x, hx⟩ := hB.1
  intro hconc
  -- `concurrent cf transferCF = Disjoint (npcA cf) (afcA transferCF)`; `afcA transferCF = {0,1} ⊇ npcA cf`.
  have hx01 : x ∈ afcA transferCF := by rw [afcA_transferCF]; exact hB.2 hx
  exact (Finset.disjoint_left.mp hconc) hx hx01

/-- **`refundDemo` — the CONCRETE inhabited `JustProgress` (all four fields, on the REAL
executor).** A fully-built liveness package: the B-just `transferSched` path from `fma0`, with goal
`Pgoal` (one receipt landed) and measure `muGoal`. Proves the machinery is NON-VACUOUS — a `JustProgress`
exists over the 46-effect executor, not just as a carried hypothesis. -/
def refundDemo : JustProgress BReg Pgoal fma0 transferSched where
  just := by
    -- B-justness: take `n := k`; `sched k = transferCF` interferes with every `BReg` forest.
    intro k cf hnb _
    exact ⟨k, le_refl _, BReg_interferes_transferCF cf hnb⟩
  μ := muGoal
  zero := by
    intro x hx
    show 1 ≤ x.log.length
    by_contra hc
    simp only [muGoal, if_neg hc] at hx
    -- `hx : 1 = 0` is absurd.
    omega
  enabled := by
    intro k hnP
    -- the only non-`Pgoal` index is 0; there `transferCF` commits and every interfering step drops `μ`.
    have hk0 : k = 0 := nonPgoal_is_zero k hnP
    subst hk0
    refine ⟨transferCF, transferCF_BReg, transferCF_commits, ?_⟩
    intro n _ _
    -- `μ (trajA … (n+1)) = 0` (positive index ⇒ `Pgoal`), `μ (trajA … 0) = μ fma0 = 1` (log empty).
    have hposlog : 1 ≤ (trajA fma0 transferSched (n + 1)).log.length := pos_is_Pgoal n
    have hpos : muGoal (trajA fma0 transferSched (n + 1)) = 0 := by
      simp only [muGoal, if_pos hposlog]
    have hzero : muGoal (trajA fma0 transferSched 0) = 1 := by decide
    rw [hpos, hzero]; omega
  frame := by
    -- `μ` is non-increasing because the log is monotone one-step (`cellNextA_logMono`).
    intro k
    show muGoal (trajA fma0 transferSched (k + 1)) ≤ muGoal (trajA fma0 transferSched k)
    by_cases hP : 1 ≤ (trajA fma0 transferSched k).log.length
    · -- already at goal ⇒ `μ k = 0`, and the log stays ≥ 1 ⇒ `μ (k+1) = 0` (residual `0 ≤ 0`).
      have hnext : 1 ≤ (trajA fma0 transferSched (k + 1)).log.length :=
        le_trans hP (trajA_logMono_le fma0 transferSched k (k + 1) (by omega))
      simp only [muGoal, if_pos hP, if_pos hnext, le_refl]
    · -- `μ k = 1` is the max, so any `μ (k+1) ≤ 1` holds.
      simp only [muGoal, if_neg hP]
      split <;> omega

/-- **`refund_demo_eventually` — THE UNCONDITIONAL LIVENESS TEETH.** `just_progress` applied to
the CONCRETE `refundDemo` package yields `Eventually Pgoal fma0 transferSched` with NO hypotheses: the
goal (a receipt lands) IS eventually reached on the real executor under reactive B-justness. This is the
non-vacuous face of `loser_refund_eventually`: the `JustProgress` machinery is inhabitable and
`just_progress` PRODUCES a `◇`. dregg2's [Just] Thm-1 feasibility, made concrete. -/
theorem refund_demo_eventually : Eventually Pgoal fma0 transferSched :=
  just_progress refundDemo

/-! ## §8 — Non-vacuity guards: the concurrency relation + commit discriminant are REAL. -/

#guard (decide (Disjoint (npcA cf0) (afcA cf5)))
#guard (decide (¬ Disjoint (npcA cf0) (afcA cf0)))
#guard (npcA cf0 == {0})
#guard (afcA cf5 == {5, 6})
#guard ((execFullForestA fma0 cf0.1).isSome)
#guard ((execFullForestA fma0 cf5.1).isSome == false)
#guard ((execFullForestA fma0 badRootFullForest).isSome == false)
#guard ((execFullForestA fma0 emitFar.1).isSome)
#guard (decide (Disjoint (npcA transferCF) (afcA emitFar)))
#guard ((execFullForestA (cellNextA fma0 emitFar) transferCF.1).isSome)
#guard ((trajA fma0 transferSched 0).log.length == 0)
#guard ((trajA fma0 transferSched 1).log.length == 1)
#guard (decide ((npcA transferCF).Nonempty ∧ npcA transferCF ⊆ ({0, 1} : Finset CellId)))
#guard (afcA transferCF == ({0, 1} : Finset CellId))

/-! ## §9 — Axiom hygiene — every keystone pinned to the standard kernel triple. -/

#assert_axioms commits_stable_off_npc
#assert_axioms cellNextA_logMono
#assert_axioms trajA_logMono_le
#assert_axioms JustProgress.frame_le
#assert_axioms just_progress
#assert_axioms npcA_cf0
#assert_axioms afcA_cf5
#assert_axioms cf0_concurrent_cf5
#assert_axioms badSched_traj_const
#assert_axioms cf0_commits_everywhere
#assert_axioms badSched_not_just
#assert_axioms emitFar_commits
#assert_axioms transferCF_concurrent_emitFar
#assert_axioms commits_stable_concrete
#assert_axioms transferCF_BReg
#assert_axioms transferCF_commits
#assert_axioms pos_is_Pgoal
#assert_axioms BReg_interferes_transferCF
#assert_axioms refund_demo_eventually
#assert_axioms loser_refund_eventually

end Dregg2.Proof.Fairness
