/-
# Dregg2.Apps.SwarmSignal — the VERIFIED ASYNC SWARM-SIGNAL coordinator (the `notify` demo app).

The demonstration of the `notify` primitive (`.docs-history-noclaude/NOTIFY-CASCADE.md` §demo-app-design): a
coordinator-agent NOTIFIES worker-agents under ATTENUATED, badge-masked notify caps — the verified
async `--wake` the metatheory previously lacked (the ADOS A2 async swarm-coordination layer made a
theorem). A worker may be poked by its coordinator on a held badge but **cannot signal back, cannot
read coordinator state, cannot widen its badge-mask, and cannot poke a peer it lacks the cap for**.

This is `AgentOrchestration`'s async sibling (`Apps/AgentOrchestration.lean`): that app dispatches
its swarm through ONE synchronous joint-turn (root + workers commit all-or-nothing); this one adds
the async EDGE — the wake that is NOT a synchronous joint turn, the `--wake` the metatheory lacked
(`NOTIFY-CASCADE.md` §Layer-5). It composes with, does not replace, the synchronous `JointTurn`.

## It runs on STEP 1's `NotifyAuthority` ALONE — WIDE-SAFE-NOW (no core change)

By design this is the early, legible demonstration (`NOTIFY-CASCADE.md` §Execution Order, item 2):
it uses `NotifyCap` / `signalGated` / `attenuateNotify` / `signalAdmissible` from
`Dregg2.Firmament.NotifyAuthority` (the committed, axiom-clean Step 1) **directly and verbatim** — it
adds **NO core `Auth.notify` constructor, NO felt-encoder arm, NO Fintype/FFI arm, NO VK bump**. It
re-USES Step 1's proven cap-algebra; it does NOT reinvent it. The app's own proof burden is the
*witnesses* — the concrete cells, caps, and `#guard` teeth on the named constellation — not
re-proving the lattice (the keystone `signalAdmissible_attenuate_no_amplify` is Step 1's, cited here).

## The honest scope of the teeth: AUTHORITY containment, NOT information containment

The six teeth below demonstrate **authority** containment: a worker holds no capability whose
target is a peer or the coordinator, so it cannot *cause* a wake on them, and the
`notificationCap_confers_at_most_notify_read` well-formedness pins that a notify cap structurally
never carries the `{Grant, Call, Reply}` authority a synchronous reply / state-read would need. They
do **NOT** claim *information* containment. A badge-OR accumulator is a classic covert channel
(`NOTIFY-CASCADE.md` §"the one risk carried forward"): a `notify` cap is **never information-free**,
even stripped of `read` — the wake itself signals "something happened," and a worker that holds a
`watch` on its OWN accumulator can still infer, from the wake's timing and badge, facts about the
coordinator's schedule. The badge-mask bounds this (an attenuation `mask₁ ⊆ mask₂` is also a
*bandwidth* attenuation — `signalAdmissible_attenuate_no_amplify` read as a bandwidth result), but
dregg has no noninterference argument yet (out-of-scope, `SeL4Abstract.lean:40`). **That gap is the
named, carried-forward risk — flagged here in the same breath as the bricks, not laundered away.**

Discipline: axiom-clean (`#assert_all_clean` at the close) — `decide`
/ `#guard` / Step-1-keystone-reuse only. `lake build Dregg2.Apps.SwarmSignal` green (LOCAL).
-/
import Dregg2.Firmament.NotifyAuthority

namespace Dregg2.Apps.SwarmSignal

open Dregg2.Firmament.SeL4Kernel (Notification ObjId)
open Dregg2.Exec.CapTPConcrete (AuthReq)
open Dregg2.Firmament.NotifyAuthority
open Dregg2.Firmament.SeL4Abstract (Auth Cap capAuthConferred)

/-! ## §0 — The swarm: a coordinator, two workers, a sub-coordinator.

Four cells (their `ObjId`s, the Rust `u64` object ids the `NotifyCap.target` carries):
  * **`coordinator`** (cell 0) — holds the root `NotifyCap` over each worker, WIDE badge-mask
    (all three task-kind bits, `0b111`);
  * **`workerA`, `workerB`** (cells 1, 2) — each a `Notification` object (a badge-OR accumulator)
    the coordinator may `signal`. Each holds, at most, a `watch` on its OWN accumulator (the
    `NOTIFY-CASCADE.md` §2.3 asymmetry: receiving your own signal needs no authority);
  * **`subCoordinator`** (cell 3) — to whom the coordinator sub-delegates "wake workerA for task-kind
    `compile` only" (an attenuated notify cap, mask `0b001`), demonstrating the delegation chain. -/

/-- The coordinator cell id (holds the root notify caps over both workers). -/
abbrev coordinator : ObjId := 0
/-- Worker A's cell id — a `Notification` badge-OR accumulator the coordinator may wake. -/
abbrev workerA : ObjId := 1
/-- Worker B's cell id — a second `Notification` accumulator. -/
abbrev workerB : ObjId := 2
/-- The sub-coordinator cell id — holds an ATTENUATED (compile-only) wake cap over workerA. -/
abbrev subCoordinator : ObjId := 3

/-! ### The badge = the task-kind. A `signal`'s badge names WHICH work the wake is for. The three
task kinds are disjoint bits in a `u64`, so a badge-mask is exactly "which kinds may I wake for". -/

/-- Task-kind `compile` — badge bit `0b001`. -/
abbrev kindCompile : Nat := 0b001
/-- Task-kind `test` — badge bit `0b010`. -/
abbrev kindTest : Nat := 0b010
/-- Task-kind `deploy` — badge bit `0b100`. -/
abbrev kindDeploy : Nat := 0b100
/-- The WIDE mask — all three task kinds (`compile ∣ test ∣ deploy = 0b111`). The coordinator's
root reach over a worker. -/
abbrev allKinds : Nat := 0b111

/-! ## §1 — The notify-cap constellation (the held authority — REUSES Step 1's `NotifyCap`).

The coordinator holds a wide cap over each worker; the sub-coordinator's cap is the coordinator's
own `coord→workerA` cap attenuated to `compile` only. NO cap targets a peer-from-a-worker or the
coordinator-from-a-worker — that ABSENCE is the structural basis of teeth 3 & 4 (§3). -/

/-- **`coordToA`** — the coordinator's root wake cap over workerA: may wake workerA for ANY of the
three task kinds (`badgeMask := allKinds = 0b111`), authorized by signature. -/
def coordToA : NotifyCap := { target := workerA, rights := .signature, badgeMask := allKinds }

/-- **`coordToB`** — the coordinator's root wake cap over workerB (same shape, different target). -/
def coordToB : NotifyCap := { target := workerB, rights := .signature, badgeMask := allKinds }

/-- **`subToA`** — the sub-coordinator's wake cap over workerA, obtained by ATTENUATING the
coordinator's `coordToA` to `compile` ONLY (`attenuateNotify coordToA .signature kindCompile`). This
is `some` (a genuine narrowing of the `0b111` mask to `0b001`) — the delegation chain. The
`subToA_def` theorem pins it; the §2 / §3 teeth exercise it. -/
def subToA : Option NotifyCap := coordToA.attenuateNotify .signature kindCompile

/-- **`capsOf holder`** — the notify caps a holder has IN THIS SCENARIO. The coordinator holds the
two root caps; the sub-coordinator holds (only) the attenuated compile-cap over workerA; the workers
hold NO notify cap at all (they are wake TARGETS, not signallers — they may only `watch` their own
accumulator, which needs no `NotifyCap`). This finite, enumerated cap-set is the structural ground
of the containment teeth (§3): a holder can signal only a target some cap of theirs names. -/
def capsOf (holder : ObjId) : List NotifyCap :=
  if holder = coordinator then [coordToA, coordToB]
  else if holder = subCoordinator then (subToA.toList)
  else []   -- workerA, workerB, and any other cell hold NO notify cap

/-! ## §2 — The sub-delegation is a genuine narrowing (REUSES Step 1's `attenuateNotify`). -/

/-- **`subToA_is_compile_only`** — the sub-delegation succeeds and yields EXACTLY the compile-only
cap: target workerA, rights `signature`, badge-mask `kindCompile = 0b001`. Witnesses that `subToA`
is `some` (the chain is live) and pins its contents. (Step-1 `attenuateNotify` on the named caps.) -/
theorem subToA_is_compile_only :
    subToA = some { target := workerA, rights := .signature, badgeMask := kindCompile } := by
  decide

/-- **`subToA_attenuation_is_strict`** — the narrowing is GENUINE (non-vacuous): the coordinator's
`coordToA` admits the `test` kind (`0b010`), but the sub-coordinator's compile-only cap does NOT.
The mask strictly shrank. The async mirror of `AgentOrchestration.worker_attenuation_is_strict`. -/
theorem subToA_attenuation_is_strict :
    coordToA.signalAdmissible kindTest = true ∧
    (∀ c, subToA = some c → c.signalAdmissible kindTest = false) := by
  decide

/-! ## §3 — THE SIX TEETH (both polarities, REUSING Step 1's `signalGated`/`attenuateNotify`).

Each tooth is the `NOTIFY-CASCADE.md` §demo-app-design item of the same number, as a Lean theorem on
the named constellation. Tooth 1 = COMMIT; teeth 2,3,4,5 = REFUSE; tooth 6 = the keystone. Every
one cites the Step-1 lemma it rests on — the app re-USES the algebra, does not re-prove it. -/

/-- **① THE COORDINATOR WAKES A WORKER ON A HELD BADGE → COMMITS, OR'ing exactly the badge.**
`signalGated coordToA n kindTest` is `some` and the accumulator gains precisely `kindTest` (the mask
is a no-op on an admissible badge, Step-1 §1). The worker then `wait`s and observes `0b010`. The
positive gate — `signalGated_commits_of_admissible`. -/
theorem coordinator_wakes_worker_commits (n : Notification) :
    signalGated coordToA n kindTest = some (n.signal kindTest) :=
  signalGated_commits_of_admissible coordToA n kindTest (by decide)

/-- **① (the observation half)** — after the committed wake, a `wait` on the (empty) accumulator
observes EXACTLY `kindTest`. The async wake is delivered: the worker sees the task-kind it was poked
for, OR'd into its badge accumulator. Reuses Step-1 `Notification.signal`/`wait`. -/
theorem worker_observes_woken_badge :
    (∃ n', signalGated coordToA Notification.empty kindTest = some n' ∧ n'.wait = (kindTest, ⟨0⟩)) := by
  refine ⟨Notification.empty.signal kindTest, coordinator_wakes_worker_commits Notification.empty, ?_⟩
  decide

/-- **② A WORKER CANNOT WIDEN ITS BADGE-MASK (no-amplification) → REFUSES.** The sub-coordinator
holds the compile-only mask (`0b001`); attempting to attenuate it to the WIDE `allKinds` (`0b111`,
adding the `test`+`deploy` bits it does not hold) is REFUSED — `attenuateNotify` returns `none`. You
cannot hand yourself (or a sub-delegate) more badge-reach than you hold. Reuses Step-1
`attenuateNotify_refuses_mask_widening`. -/
theorem worker_cannot_widen_mask (c : NotifyCap) (h : subToA = some c) :
    c.attenuateNotify .signature allKinds = none := by
  -- `c` is the compile-only cap (mask 0b001); widening to allKinds (0b111) adds bits not held.
  have hc : c = { target := workerA, rights := .signature, badgeMask := kindCompile } := by
    rw [subToA_is_compile_only] at h; exact (Option.some.injEq _ _).mp h.symm
  subst hc
  exact attenuateNotify_refuses_mask_widening _ .signature allKinds (by decide)

/-- **③ A WORKER CANNOT POKE A PEER IT LACKS THE CAP FOR → STRUCTURALLY UNREACHABLE.** The
sub-coordinator's ONLY notify cap targets workerA (`capsOf subCoordinator = [subToA-cap]`); NO cap of
its targets workerB. So there is no `signalGated cap workerB-accum …` to construct from its caps — it
cannot cause a wake on a cell it holds no cap over. We state this as: every cap the sub-coordinator
holds has `target = workerA ≠ workerB` — the wake-set excludes the peer. (Structural, not incidental:
a holder can signal only a target some held cap names.) -/
theorem worker_cannot_poke_peer :
    ∀ c ∈ capsOf subCoordinator, c.target ≠ workerB := by
  decide

/-- **③ (non-vacuity)** — the sub-coordinator DOES hold a cap (over workerA), so the ∀ above is not
vacuous: the wake-set is non-empty, it just excludes the peer. -/
theorem subCoordinator_holds_a_cap :
    ∃ c, c ∈ capsOf subCoordinator ∧ c.target = workerA := by
  decide

/-- **④ A WORKER CANNOT SIGNAL BACK / READ COORDINATOR STATE → STRUCTURALLY UNREACHABLE (two legs).**
*Leg (a) — no cap targets the coordinator.* A worker (here the sub-coordinator, the only non-root
holder) holds no `NotifyCap` whose target is `coordinator`, so it cannot cause a wake on the
coordinator: every held cap's target is `≠ coordinator`. *Leg (b) — a notify cap structurally cannot
carry a reply/read authority.* Even the coordinator's own caps are `notify`-authority: a notification
cap confers at most `{Reset, Receive, Notify}` and NEVER `{Grant, Call, Reply}` (Step-1
`notificationCap_confers_at_most_notify_read`), so no notify cap — held by anyone — confers the
synchronous `Reply`/`Call` a "signal back" or a state-read would require. Async-no-reply is enforced
by the authority shape, not merely by this scenario's wiring. -/
theorem worker_cannot_signal_back :
    -- leg (a): no held cap targets the coordinator (the async wake has no back-edge here)
    (∀ c ∈ capsOf subCoordinator, c.target ≠ coordinator) ∧
    (∀ c ∈ capsOf workerA, c.target ≠ coordinator) ∧
    -- leg (b): a notification cap NEVER confers Call/Reply — async-no-reply is structural
    (∀ (oref badge : Nat) (r : Dregg2.Firmament.SeL4Abstract.CapRights),
      Auth.Reply ∉ capAuthConferred (.NotificationCap oref badge r) ∧
      Auth.Call ∉ capAuthConferred (.NotificationCap oref badge r)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro oref badge r
  exact ⟨notificationCap_never_reply oref badge r, notificationCap_never_call oref badge r⟩

/-- **⑤ AN OUT-OF-MASK SIGNAL IS REFUSED (fail-closed) → REFUSES.** The sub-coordinator's compile-only
cap (mask `0b001`) is asked to wake workerA for the `test` kind (`0b010`, outside the mask):
`signalGated subToA-cap n kindTest` is `none`. The wake is refused, fail-closed — you cannot signal a
badge you do not hold. Reuses Step-1 `signalGated_refuses_of_inadmissible`. -/
theorem out_of_mask_signal_refused (c : NotifyCap) (n : Notification) (h : subToA = some c) :
    signalGated c n kindTest = none := by
  have hc : c = { target := workerA, rights := .signature, badgeMask := kindCompile } := by
    rw [subToA_is_compile_only] at h; exact (Option.some.injEq _ _).mp h.symm
  subst hc
  exact signalGated_refuses_of_inadmissible _ n kindTest (by decide)

/-- **⑥ ATTENUATION STRICTLY SHRINKS THE ADMITTED BADGES → THE KEYSTONE.** Every badge the
sub-coordinator's attenuated cap can signal, the coordinator's original cap could too — attenuation
only shrinks the admissible set, never grows it. This is Step-1's non-amplification keystone
`signalAdmissible_attenuate_no_amplify` applied to the `coordToA → subToA` delegation edge. (Strict:
§2 `subToA_attenuation_is_strict` witnesses a badge — `test` — the parent admits and the child does
not, so the shrink is genuine, not equality.) -/
theorem attenuation_shrinks_admitted (c : NotifyCap) (h : subToA = some c)
    (badge : Nat) (hadm : c.signalAdmissible badge = true) :
    coordToA.signalAdmissible badge = true :=
  signalAdmissible_attenuate_no_amplify coordToA .signature kindCompile c h badge hadm

/-! ## §4 — Conservation: every wake is balance-NEUTRAL (it writes a badge accumulator, not the
ledger). A `signal` OR's a badge into a `Notification` — it moves no asset, mints nothing, burns
nothing. The "conservation" of this app is the simplest possible: the wake touches the async-signal
object only. We pin it as: a committed wake yields a `Notification` (a pure badge accumulator), and
its badge differs from the prior only by the OR'd-in (masked) badge — no other state, no ledger. -/

/-- **`wake_is_balance_neutral`** — a committed wake produces a `Notification` whose badge is exactly
the prior OR the (admissible, so un-truncated) signalled badge — and NOTHING else changes. The
async-signal object is the only state a wake touches; there is no ledger column, no asset, in a
`Notification`. (The §demo-app-design "conservation" point: a wake writes a badge accumulator, not
the ledger — here, definitionally, because the wake's codomain IS the accumulator.) -/
theorem wake_is_balance_neutral (n : Notification) (badge : Nat)
    (hadm : coordToA.signalAdmissible badge = true) :
    ∃ n', signalGated coordToA n badge = some n' ∧ n'.badge = n.badge ||| badge := by
  refine ⟨n.signal badge, signalGated_commits_of_admissible coordToA n badge hadm, ?_⟩
  rfl

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the six teeth BITE on the concrete swarm, both polarities. -/

section Witnesses

-- ① COMMIT: the coordinator wakes workerA for `test` ⇒ `signalGated` is `some`, OR'ing 0b010 in.
#guard (signalGated coordToA Notification.empty kindTest).isSome
#guard signalGated coordToA Notification.empty kindTest == some (Notification.empty.signal kindTest)
-- ① and the woken worker `wait`s and OBSERVES exactly the badge it was poked for (the wake delivered).
#guard
  match signalGated coordToA Notification.empty kindTest with
  | some n' => n'.wait == (kindTest, (⟨0⟩ : Notification))
  | none => false
-- ① the coordinator may wake for ALL three kinds (the wide mask admits each).
#guard (signalGated coordToA Notification.empty kindCompile).isSome
#guard (signalGated coordToA Notification.empty kindDeploy).isSome

-- ② REFUSE: the compile-only sub-coordinator cannot widen its mask to allKinds (0b111) ⇒ none.
#guard
  match subToA with
  | some c => (c.attenuateNotify .signature allKinds).isNone
  | none => false
-- ② it CAN, however, re-narrow to the empty mask (0) — attenuation is not constant-none, it narrows.
#guard
  match subToA with
  | some c => (c.attenuateNotify .signature 0).isSome
  | none => false

-- ③ REFUSE (structural): NONE of the sub-coordinator's caps target workerB (the peer) …
#guard (capsOf subCoordinator).all (fun c => c.target != workerB)
-- ③ … but it DOES hold a cap (over workerA) — the wake-set is non-empty, it just excludes the peer.
#guard (capsOf subCoordinator).any (fun c => c.target == workerA)
-- ③ a worker (workerA) holds NO notify cap at all — it is a wake TARGET, not a signaller.
#guard (capsOf workerA).isEmpty

-- ④ REFUSE (structural): no held cap of the sub-coordinator (nor of a worker) targets the coordinator
-- — the async wake has no back-edge in this scenario.
#guard (capsOf subCoordinator).all (fun c => c.target != coordinator)
#guard (capsOf workerA).all (fun c => c.target != coordinator)
-- ④ (leg b) a notification cap confers Notify but NEVER Reply/Call (async-no-reply, structurally) —
-- even with FULL rights the synchronous reply/call authority is stripped.
#guard (Auth.Notify ∈ capAuthConferred (.NotificationCap workerA kindTest [.AllowWrite]) : Bool)
#guard !(Auth.Reply ∈ capAuthConferred (.NotificationCap workerA kindTest Dregg2.Firmament.SeL4Abstract.allRights) : Bool)
#guard !(Auth.Call ∈ capAuthConferred (.NotificationCap workerA kindTest Dregg2.Firmament.SeL4Abstract.allRights) : Bool)

-- ⑤ REFUSE (fail-closed): the compile-only cap signalling the `test` kind (out of mask) ⇒ none.
#guard
  match subToA with
  | some c => (signalGated c Notification.empty kindTest).isNone
  | none => false
-- ⑤ but the SAME cap signalling its held `compile` kind COMMITS (the gate is not constant-none).
#guard
  match subToA with
  | some c => (signalGated c Notification.empty kindCompile).isSome
  | none => false

-- ⑥ KEYSTONE (witnessed, both polarities): the sub-coordinator admits `compile` …
#guard
  match subToA with
  | some c => c.signalAdmissible kindCompile
  | none => false
-- ⑥ … the coordinator admits it too (no-amplification: child ⊆ parent on the admissible set) …
#guard coordToA.signalAdmissible kindCompile
-- ⑥ … and STRICTLY: the coordinator admits `test`/`deploy` the sub-coordinator does NOT (genuine shrink).
#guard coordToA.signalAdmissible kindTest && coordToA.signalAdmissible kindDeploy
#guard
  match subToA with
  | some c => !c.signalAdmissible kindTest && !c.signalAdmissible kindDeploy
  | none => false

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing theorem checked kernel-clean (only the standard
`propext`/`Classical.choice`/`Quot.sound`). -/

#assert_all_clean [
  subToA_is_compile_only,
  subToA_attenuation_is_strict,
  coordinator_wakes_worker_commits,
  worker_observes_woken_badge,
  worker_cannot_widen_mask,
  worker_cannot_poke_peer,
  subCoordinator_holds_a_cap,
  worker_cannot_signal_back,
  out_of_mask_signal_refused,
  attenuation_shrinks_admitted,
  wake_is_balance_neutral
]

end Dregg2.Apps.SwarmSignal
