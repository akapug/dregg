/-
# Dregg2.Firmament.NotifyAuthority — async-signal AS a held capability (the `notify` brick, STEP 1).

This module is the **transfer triangle** of the `notify` primitive (`docs/NOTIFY-PRIMITIVE.md`):
it makes the *cap-algebra on async-signal authority* a THEOREM **before** the core `Auth` inductive
(`Authority/Positional.lean:37`) is touched. It adds NO core-`Auth` constructor, NO felt/Fintype/FFI
arm, NO VK bump — those are STEP 2 (the `Auth.notify` core edit + α-totalization, held for ember).
Here we work entirely firmament-locally, reusing what already exists.

## The hole this names (the census, in one line)

dregg runs async notification in at least five real places (the seL4 `Notification`, the inbox, the
pubsub broadcast, the dynamics stream, the blocklace `finality_notify`) and **not one expresses the
authority to signal as a held capability**. The seL4→Lean transcription found exactly this as the
single genuine projection-loss (`SeL4Abstract.lean:459`, `Notify ↦ none`): the firmament models a
`Notification` object distinctly from an `Endpoint`, but a cap to either confers the same dregg
authority, because dregg `Auth` has no `notify`. `notify` is the missing async dual of the synchronous
endpoint `write`/`call`: the pure "I may WAKE you" authority — no read, no synchronous message body, no
reply.

## We WELD — the Notification object EXISTS, disconnected; we connect a cap to it (do NOT reinvent)

Three things already exist and are REUSED verbatim (no new lattice, no new badge object):

  * `Dregg2.Firmament.SeL4Kernel.Notification` — the badge-OR accumulator (`signal n badge :=
    { badge := n.badge ||| badge }`, `wait` = read-and-clear), already green-refined against the Rust
    `EmulatedKernel::signal`/`wait` (`SeL4Kernel.lean:236`+, theorems `signal_then_wait` /
    `wait_observes_badge_or` / `second_wait_is_zero`). `signalGated` below is a cap-gated WRAPPER over
    this exact `Notification.signal` — it does not re-implement the accumulator.
  * `Dregg2.Exec.CapTPConcrete.facetAttenuation` — the `u32`-mask bit-subset decision
    `(child &&& parent) == child` (`CapTPConcrete.lean:146`, the Rust `is_facet_attenuation`), already
    reflexive (`facetAttenuation_refl`, via `Nat.and_self`) with `0` the bottom
    (`facetAttenuation_zero_bot`). **The badge mask is exactly this sub-lattice** — "may signal, but
    only badge ⊑ X" is `facetAttenuation X badge` (badge's bits are within the mask). We REUSE it as
    the badge order and complete it to a genuine partial order (antisymmetry + transitivity below),
    mirroring how `authNarrowerOrEqual` is proven a partial order.
  * `Dregg2.Firmament.CapGradation.grantOk` (= `authNarrowerOrEqual granted held`, the Rust
    `is_attenuation`) — the ONE non-amplification decision the firmament `mint` gate already proves
    non-amplifying (`SeL4Kernel.lean:175`). A `NotifyCap` carries an `AuthReq` rights field (the seL4
    `NotificationCap oref badge cap_rights` shape, `SeL4Abstract.lean:149`), so its RIGHTS attenuation
    rides `grantOk` verbatim; the badge mask is the ADDITIONAL payload-scope sub-lattice. Attenuation
    narrows BOTH (`attenuateNotify`), refusing a widening on either.

So the design's "the badge-mask is the SAME `granted ⊆ held` order the mint already proves
non-amplifying" is structural here: the mask order IS `facetAttenuation` (the same `u32`-mask leg the
handoff validator runs, `handoffNonAmplifyingC`'s effect-mask facet), and the rights order IS the same
`grantOk` the mint gates on. We add no order — we instantiate two existing ones on a notification cap.

## What is proven

  1. **NON-AMPLIFICATION (the badge mask is a sub-lattice).** `maskNarrowerOrEqual` (= `facetAttenuation`)
     is a genuine partial order on the badge lattice (reflexive / antisymmetric / transitive, `0` ⊥).
     `attenuateNotify` narrows the mask (and the rights) only by that order; the keystone
     `signalGated_attenuate_no_amplify` shows a signal admissible through the ATTENUATED (narrower-mask)
     cap is admissible through the original — narrowing the mask only SHRINKS the admissible badge set.
     A widening (a mask with a bit not held) is REFUSED by `attenuateNotify` (`none`).
  2. **GATE TEETH (both polarities).** `signalGated` COMMITS (`some`, OR'ing the masked badge into the
     accumulator) iff the signalled badge is within the held mask, and REFUSES (`none`) a badge with a
     bit outside the mask — both `#guard`'d. The attenuated `[.notify]` ("may poke, may not message")
     is EXPRESSIBLE and DISTINCT from `write`: a `NotifyCap`'s conferred authority contains `Notify` but
     NOT `SyncSend` (the synchronous send) — the new expressivity the design names.
  3. **WELL-FORMEDNESS (seL4-faithful).** A notification cap (`SeL4Abstract.Cap.NotificationCap`)
     confers at most `{Reset, Receive, Notify}` — never `{Grant, Call, Reply}` — exactly the
     `SeL4Abstract.lean:225` strip (the `NotificationCap` case filters `AllowGrant`/`AllowGrantReply`
     before `capRightsToAuth`). And `Notify` is distinct from the synchronous `SyncSend`/`Call`/`Reply`,
     so the async wake is a genuinely separate authority from the sync write/call/reply.

NON-VACUITY both polarities (`#guard` teeth that BITE): a within-mask signal COMMITS with the masked
badge OR'd; an out-of-mask signal REFUSES; attenuation to a narrower mask COMMITS and the narrower cap
admits strictly fewer badges; a widening attenuation REFUSES; `Notify ∈` / `SyncSend ∉` a notification
cap's authority.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` — `decide`
/ `#guard` / `rw`-over-`Nat.and_*` only. `lake build` green (LOCAL). NO core-`Auth` edit; NO felt
encoder touched. ObjId/badge are `Nat` (the Rust `u64` object id / `u64` badge), as in `SeL4Kernel`.
-/
import Dregg2.Firmament.SeL4Kernel
import Dregg2.Firmament.SeL4Abstract
import Dregg2.Exec.CapTPConcrete
import Dregg2.Tactics

namespace Dregg2.Firmament.NotifyAuthority

open Dregg2.Firmament.SeL4Kernel (Notification ObjId)
open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual facetAttenuation)
open Dregg2.Firmament (grantOk)

/-! ## §1 — The badge-mask sub-lattice (REUSED from `facetAttenuation`, completed to a partial order).

The badge a `signal` carries is a `u64` discriminator (scope / membership / fault — the seL4 badge).
A `notify` cap's reach is a **badge mask**: "may signal, but only badge ⊑ `badgeMask`". "badge ⊑ mask"
means the signalled bits are a SUBSET of the mask's bits — exactly `facetAttenuation mask badge`
(`badge &&& mask == badge`), the SAME `u32`-mask bit-subset the captp handoff validator runs
(`CapTPConcrete.lean:146`). We REUSE it as the badge order and prove it a genuine partial order — the
same shape as `authNarrowerOrEqual`'s order — so "the badge mask is a sub-lattice" is a theorem. -/

/-- **`maskNarrowerOrEqual m₁ m₂`** — `m₁` is narrower-than-or-equal to `m₂` on the badge lattice:
`m₁`'s bits are a SUBSET of `m₂`'s (`m₁ ⊆ m₂`). This IS `facetAttenuation m₂ m₁` (the reused
`u32`-mask bit-subset, `child ⊆ parent`); we name it on the badge to read as the cap-attenuation order
"the narrower mask is within the wider". A notify cap attenuates by narrowing the mask under THIS
order. -/
def maskNarrowerOrEqual (m₁ m₂ : Nat) : Bool := facetAttenuation m₂ m₁

/-- **`badgeWithinMask badge mask`** — the signalled `badge` is within the cap's `mask` (admissible):
its bits are a subset of the mask's (`badge ⊆ mask`). This is `facetAttenuation mask badge`. The
admissibility predicate the gate runs. -/
def badgeWithinMask (badge mask : Nat) : Bool := facetAttenuation mask badge

/-- Reflexivity: a mask is narrower-or-equal to itself (REUSES `facetAttenuation_refl`). -/
theorem maskNarrowerOrEqual_refl (m : Nat) : maskNarrowerOrEqual m m = true :=
  Dregg2.Exec.CapTPConcrete.facetAttenuation_refl m

/-- The empty mask `0` ("may signal NOTHING") is the BOTTOM — narrower than every mask (REUSES
`facetAttenuation_zero_bot`). A fully-revoked notify cap signals nothing. (`maskNarrowerOrEqual 0 m =
facetAttenuation m 0`, the bit-subset `0 ⊆ m`.) -/
theorem maskNarrowerOrEqual_zero_bot (m : Nat) : maskNarrowerOrEqual 0 m = true :=
  Dregg2.Exec.CapTPConcrete.facetAttenuation_zero_bot m

/-- Antisymmetry: mutual narrower-or-equal forces equality — the badge order has no cycle (a buggy
`m₁ ⊆ m₂ ∧ m₂ ⊆ m₁` with `m₁ ≠ m₂` would be a mask-amplification loophole). Via `Nat.and_comm`. -/
theorem maskNarrowerOrEqual_antisymm {m₁ m₂ : Nat}
    (h₁ : maskNarrowerOrEqual m₁ m₂ = true) (h₂ : maskNarrowerOrEqual m₂ m₁ = true) :
    m₁ = m₂ := by
  simp only [maskNarrowerOrEqual, facetAttenuation, beq_iff_eq] at h₁ h₂
  -- h₁ : m₁ &&& m₂ = m₁ ,  h₂ : m₂ &&& m₁ = m₂  ⊢  m₁ = m₂
  rw [← h₁, Nat.and_comm, h₂]

/-- Transitivity: chaining two mask-narrowings is a narrowing — the closure property a delegation
chain needs (sub-delegating "wake for kind K" twice stays within the original mask). Via
`Nat.and_assoc`. -/
theorem maskNarrowerOrEqual_trans {m₁ m₂ m₃ : Nat}
    (h₁ : maskNarrowerOrEqual m₁ m₂ = true) (h₂ : maskNarrowerOrEqual m₂ m₃ = true) :
    maskNarrowerOrEqual m₁ m₃ = true := by
  simp only [maskNarrowerOrEqual, facetAttenuation, beq_iff_eq] at h₁ h₂ ⊢
  -- h₁ : m₁ &&& m₂ = m₁ , h₂ : m₂ &&& m₃ = m₂  ⊢  m₁ &&& m₃ = m₁
  rw [← h₁, Nat.and_assoc, h₂]

/-- **The admissible-set is MONOTONE in the mask** — the load-bearing non-amplification step on the
badge lattice: if `mask' ⊆ mask` and a badge is within the NARROWER `mask'`, it is within `mask` too.
So narrowing the mask only SHRINKS the admissible badge set (never grows it). Via `Nat.and_assoc`. -/
theorem badgeWithinMask_mono {badge mask mask' : Nat}
    (hsub : maskNarrowerOrEqual mask' mask = true)
    (hadm : badgeWithinMask badge mask' = true) :
    badgeWithinMask badge mask = true := by
  simp only [maskNarrowerOrEqual, badgeWithinMask, facetAttenuation, beq_iff_eq] at hsub hadm ⊢
  -- hsub : mask' &&& mask = mask' , hadm : badge &&& mask' = badge  ⊢  badge &&& mask = badge
  rw [← hadm, Nat.and_assoc, hsub]

/-- When a badge is within the mask, masking it is a no-op (`badge &&& mask = badge`) — so a committed
signal OR's in EXACTLY the badge, not a truncated one. The bridge from the admissibility predicate to
the `signal` value. -/
theorem masked_eq_badge_of_within {badge mask : Nat}
    (hadm : badgeWithinMask badge mask = true) :
    badge &&& mask = badge := by
  simpa only [badgeWithinMask, facetAttenuation, beq_iff_eq] using hadm

/-! ## §2 — The `NotifyCap`: the right to WAKE a target (the async dual of the endpoint call).

Mirrors seL4's `NotificationCap oref badge cap_rights` (`SeL4Abstract.lean:149`): a target object, the
held `cap_rights` (the SAME `AuthReq` lattice the firmament mint gates on), and the badge-mask scope.
Holding `NotifyCap target rights mask` means: *you may `signal` `target` with a badge ⊑ `mask`, and
nothing else* — no read, no synchronous send, no reply (that is the §3 well-formedness). -/

/-- **`NotifyCap`** — a held capability to cause a WAKE on `target`, scoped to badges within
`badgeMask`. The `rights : AuthReq` field carries the seL4 cap-rights (so the rights attenuation rides
the existing `grantOk`); the `badgeMask : Nat` is the payload-scope sub-lattice (§1). This is the
async dual of an endpoint-call cap: it confers the right to poke, not to message. -/
structure NotifyCap where
  /-- The notification object this cap may signal — the Rust `u64` `ObjectId`. -/
  target : ObjId
  /-- The held seL4 cap-rights (the SAME `AuthReq` the firmament mint gates on). For a well-formed
  notify cap these confer at most `{notify, read}` (§3). -/
  rights : AuthReq
  /-- The badge-mask scope: a `signal` is admissible iff its badge ⊑ `badgeMask` (§1). -/
  badgeMask : Nat
  deriving Repr, DecidableEq

namespace NotifyCap

/-- **`signalAdmissible cap badge`** — may `cap` signal this `badge`? Iff the badge's bits are within
the cap's `badgeMask` (`badge ⊑ badgeMask`). The §1 admissibility predicate, on the cap. -/
def signalAdmissible (cap : NotifyCap) (badge : Nat) : Bool := badgeWithinMask badge cap.badgeMask

/-- **`attenuateNotify cap narrowerRights narrowerMask`** — narrow a notify cap on BOTH axes, gated on
the EXISTING orders: the rights by `grantOk cap.rights narrowerRights` (= the firmament mint's
`granted ⊆ held`, REUSED), the badge mask by `maskNarrowerOrEqual narrowerMask cap.badgeMask` (= the
`u32`-mask bit-subset, REUSED). Returns the narrowed cap, or `none` if EITHER axis would amplify (a
rights widening OR a mask with a bit not held). This is the cap-algebra attenuation the design's §2.2
names — and it is the same two `granted ⊆ held` orders already proven non-amplifying. -/
def attenuateNotify (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat) :
    Option NotifyCap :=
  if grantOk cap.rights narrowerRights ∧ maskNarrowerOrEqual narrowerMask cap.badgeMask then
    some { target := cap.target, rights := narrowerRights, badgeMask := narrowerMask }
  else
    none

end NotifyCap

/-- **`signalGated cap n badge`** — the cap-gated WRAPPER over the existing
`SeL4Kernel.Notification.signal` (`SeL4Kernel.lean:250`). A signal is permitted iff the holder's
`NotifyCap` admits the badge (`badge ⊑ badgeMask`); when permitted, it OR's the **masked** badge
(`badge &&& badgeMask`, which equals `badge` exactly when admissible, §1) into the accumulator via the
unchanged `Notification.signal`; otherwise it REFUSES (`none`). The async-signal authority, expressed
as a gate over the badge-OR object — NOT a re-implementation of it. -/
def signalGated (cap : NotifyCap) (n : Notification) (badge : Nat) : Option Notification :=
  if cap.signalAdmissible badge then
    some (n.signal (badge &&& cap.badgeMask))
  else
    none

/-! ## §3 — NON-AMPLIFICATION: attenuating a notify cap only SHRINKS what it can signal.

`attenuateNotify` narrows by the two existing `granted ⊆ held` orders (rights via `grantOk`, mask via
`maskNarrowerOrEqual`); a widening on either axis is REFUSED. The keystone: a badge admissible through
the ATTENUATED (narrower-mask) cap is admissible through the original — so a holder who attenuates can
signal a SUBSET of what it could before. A `signal` of a badge outside the held mask is REFUSED.

This is the firmament `mint`'s non-amplification (`mint_child_attenuates_parent` /
`mint_refuses_amplification`), now on the badge lattice: a notify cap attenuates by narrowing the
badge-mask, and a widening (signalling a badge not held / handing out more badge-reach than held) is
refused. -/

/-- **ATTENUATE NARROWS BOTH AXES** (the positive direction): when `attenuateNotify` succeeds, the
result holds EXACTLY the requested narrower rights and mask, both `⊆` the original (`grantOk` on the
rights, `maskNarrowerOrEqual` on the mask) — a genuine attenuation on both, never an amplification. -/
theorem attenuateNotify_narrows
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat) (out : NotifyCap)
    (h : cap.attenuateNotify narrowerRights narrowerMask = some out) :
    out.rights = narrowerRights ∧ out.badgeMask = narrowerMask
      ∧ grantOk cap.rights narrowerRights = true
      ∧ maskNarrowerOrEqual narrowerMask cap.badgeMask = true := by
  unfold NotifyCap.attenuateNotify at h
  by_cases hgate : grantOk cap.rights narrowerRights ∧ maskNarrowerOrEqual narrowerMask cap.badgeMask
  · rw [if_pos hgate] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, hgate.1, hgate.2⟩
  · rw [if_neg hgate] at h
    exact absurd h (by simp)

/-- **ATTENUATE REFUSES A MASK WIDENING** (the negative direction, badge axis): a mask with a bit NOT
in the held mask (`¬ maskNarrowerOrEqual narrowerMask cap.badgeMask`) is REFUSED — `attenuateNotify`
returns `none`. Handing out more badge-reach than you hold is rejected, exactly as `seL4_CNode_Mint`
rejects an over-broad rights mask. -/
theorem attenuateNotify_refuses_mask_widening
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat)
    (hwiden : maskNarrowerOrEqual narrowerMask cap.badgeMask = false) :
    cap.attenuateNotify narrowerRights narrowerMask = none := by
  unfold NotifyCap.attenuateNotify
  rw [if_neg]
  rintro ⟨_, hm⟩
  rw [hwiden] at hm
  exact absurd hm (by simp)

/-- **ATTENUATE REFUSES A RIGHTS WIDENING** (the negative direction, rights axis): a rights widening
(`¬ grantOk cap.rights narrowerRights`) is REFUSED — the SAME `granted ⊆ held` the firmament mint
enforces, now on the notify cap's rights. -/
theorem attenuateNotify_refuses_rights_widening
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat)
    (hwiden : grantOk cap.rights narrowerRights = false) :
    cap.attenuateNotify narrowerRights narrowerMask = none := by
  unfold NotifyCap.attenuateNotify
  rw [if_neg]
  rintro ⟨hr, _⟩
  rw [hwiden] at hr
  exact absurd hr (by simp)

/-- **THE NON-AMPLIFICATION KEYSTONE.** A badge admissible through the ATTENUATED (narrower-mask) cap
is admissible through the ORIGINAL cap. So attenuating a notify cap can only SHRINK the set of badges
it may signal — it never lets the holder wake with a badge the parent could not. (The mask narrowed,
so `badgeWithinMask_mono` lifts admissibility from the child mask up to the parent mask.) This is the
async-signal mirror of `mint_child_attenuates_parent`. -/
theorem signalAdmissible_attenuate_no_amplify
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat) (out : NotifyCap)
    (hatten : cap.attenuateNotify narrowerRights narrowerMask = some out)
    (badge : Nat) (hadm : out.signalAdmissible badge = true) :
    cap.signalAdmissible badge = true := by
  obtain ⟨_, hmask, _, hsub⟩ := attenuateNotify_narrows cap narrowerRights narrowerMask out hatten
  simp only [NotifyCap.signalAdmissible] at hadm ⊢
  rw [hmask] at hadm
  exact badgeWithinMask_mono hsub hadm

/-- **A SIGNAL WITHIN THE HELD MASK COMMITS, OR'ing EXACTLY the badge** (the positive gate): if the
badge is admissible, `signalGated` returns `some` and the accumulator gains precisely `badge` (the
mask is a no-op on an admissible badge, §1) — the cap-gated wake delivers the full intended badge. -/
theorem signalGated_commits_of_admissible
    (cap : NotifyCap) (n : Notification) (badge : Nat)
    (hadm : cap.signalAdmissible badge = true) :
    signalGated cap n badge = some (n.signal badge) := by
  unfold signalGated
  rw [if_pos hadm]
  have : badge &&& cap.badgeMask = badge :=
    masked_eq_badge_of_within (by simpa [NotifyCap.signalAdmissible] using hadm)
  rw [this]

/-- **A SIGNAL OUTSIDE THE HELD MASK IS REFUSED** (the negative gate): a badge with a bit outside the
mask (`¬ signalAdmissible`) makes `signalGated` return `none` — the wake is refused, fail-closed. This
is the gate tooth: you cannot signal a badge you do not hold. -/
theorem signalGated_refuses_of_inadmissible
    (cap : NotifyCap) (n : Notification) (badge : Nat)
    (hinadm : cap.signalAdmissible badge = false) :
    signalGated cap n badge = none := by
  unfold signalGated
  rw [if_neg]
  rw [hinadm]; simp

/-! ## §4 — WELL-FORMEDNESS: a notification cap confers at most `{notify, read}` (seL4-faithful).

The §3 gate makes `notify` a held authority; this section pins that it is the RIGHT authority and a
DISTINCT one. We work over the transcribed-seL4 `SeL4Abstract.Cap`/`Auth`/`capAuthConferred` (which
already has `.Notify`/`.Receive` — the seL4-faithful 12-ctor enum, NOT the core dregg `Auth`, so this
touches no Step-2 surface). The fact: an seL4 `NotificationCap` confers at most `{Reset, Receive,
Notify}` — never `{Grant, Call, Reply}` — because the `NotificationCap` case of `capAuthConferred`
filters out `AllowGrant`/`AllowGrantReply` BEFORE `capRightsToAuth` (`SeL4Abstract.lean:225`). And
`Notify` is distinct from the synchronous `SyncSend`/`Call`/`Reply`: the async wake is a separate
authority from the sync write/call/reply — the new corner `notify` carves. -/

open Dregg2.Firmament.SeL4Abstract (Auth Cap capAuthConferred)

/-- The authorities a WELL-FORMED notification cap may confer: the always-on `Reset`, the badge-`wait`
`Receive` (the async "read"), and the `Notify` wake. NEVER `Grant`/`Call`/`Reply` (those are the
synchronous-endpoint / grant authorities a Notification cap must not carry). -/
def notifyConferrable : List Auth := [.Reset, .Receive, .Notify]

/-- **A NOTIFICATION CAP CONFERS AT MOST `{Reset, Receive, Notify}`** — for ANY badge / rights, every
authority an seL4 `NotificationCap` confers is in `notifyConferrable`. This IS the `SeL4Abstract.lean:225`
strip as a dregg fact: the `r - {AllowGrant, AllowGrantReply}` filter means `AllowGrant` (⇒ all auths)
and `AllowGrantReply ∧ AllowWrite` (⇒ `Call`) can never fire, so only `Reset` / `Receive` (from
`AllowRead`) / `Notify` (from `AllowWrite`, async since `sync = false`) survive. The "may poke, may not
message/grant/reply" authority, pinned. -/
theorem notificationCap_confers_at_most_notify_read
    (oref badge : Nat) (r : SeL4Abstract.CapRights) :
    capAuthConferred (.NotificationCap oref badge r) ⊆ notifyConferrable := by
  intro a ha
  -- `capAuthConferred (NotificationCap …) = capRightsToAuth (r.filter …) false`; the filter drops
  -- AllowGrant/AllowGrantReply, so only [Reset] ++ (AllowRead?→Receive) ++ (AllowWrite?→Notify) remain.
  -- after the filter, `contains AllowGrant` and `contains AllowGrantReply` are both false, collapsing
  -- the `allAuth` and `Call` clauses to `[]`; `a` is then `Reset`, or `Receive`, or `Notify`.
  have hng : (r.filter (fun x => x ≠ .AllowGrant ∧ x ≠ .AllowGrantReply)).contains .AllowGrant
      = false := by
    simp [List.contains_eq_mem, List.mem_filter]
  have hngr : (r.filter (fun x => x ≠ .AllowGrant ∧ x ≠ .AllowGrantReply)).contains .AllowGrantReply
      = false := by
    simp [List.contains_eq_mem, List.mem_filter]
  simp only [capAuthConferred, SeL4Abstract.capRightsToAuth, hng, hngr, Bool.false_eq_true,
    if_false, false_and, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, List.mem_ite_nil_right, notifyConferrable] at ha ⊢
  -- ha is now: a = Reset ∨ (AllowRead ∈ r ∧ a = Receive) ∨ (AllowWrite ∈ r ∧ a = Notify);
  -- the goal: a = Reset ∨ a = Receive ∨ a = Notify — drop the right-hand conjuncts.
  tauto

/-- **NEVER `Grant`** — a notification cap confers no `Grant` authority (it cannot hand out grant
rights). A direct corollary of the at-most bound: `Grant ∉ notifyConferrable`. -/
theorem notificationCap_never_grant
    (oref badge : Nat) (r : SeL4Abstract.CapRights) :
    Auth.Grant ∉ capAuthConferred (.NotificationCap oref badge r) := by
  intro hmem
  have := notificationCap_confers_at_most_notify_read oref badge r hmem
  simp [notifyConferrable] at this

/-- **NEVER `Call`** — a notification cap confers no synchronous-`Call` authority (no RPC request).
The async dual has no synchronous call. -/
theorem notificationCap_never_call
    (oref badge : Nat) (r : SeL4Abstract.CapRights) :
    Auth.Call ∉ capAuthConferred (.NotificationCap oref badge r) := by
  intro hmem
  have := notificationCap_confers_at_most_notify_read oref badge r hmem
  simp [notifyConferrable] at this

/-- **NEVER `Reply`** — a notification cap confers no `Reply` authority. The async send has no reply
(the design's §2.3 asymmetry: `notify` is the send-with-no-reply corner). -/
theorem notificationCap_never_reply
    (oref badge : Nat) (r : SeL4Abstract.CapRights) :
    Auth.Reply ∉ capAuthConferred (.NotificationCap oref badge r) := by
  intro hmem
  have := notificationCap_confers_at_most_notify_read oref badge r hmem
  simp [notifyConferrable] at this

/-- **`notify` IS DISTINCT from the synchronous write/call/reply.** The `Notify` authority is a
DIFFERENT enum constructor from `SyncSend` (synchronous send), `Call`, and `Reply` — so the async wake
is a genuinely separate authority, not a relabelling of the sync write. This is the seL4 split
(`SeL4Abstract.lean:182`: same `AllowWrite` bit ⇒ `SyncSend` on an Endpoint, `Notify` on a
Notification) at the authority level. -/
theorem notify_distinct_from_sync :
    Auth.Notify ≠ Auth.SyncSend ∧ Auth.Notify ≠ Auth.Call ∧ Auth.Notify ≠ Auth.Reply := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **A NOTIFICATION CAP GENUINELY CONFERS `Notify`, NOT `SyncSend`** (non-vacuity of the
distinction): a notification cap whose rights include `AllowWrite` confers `Notify` (the async wake),
while the SAME `AllowWrite` on an ENDPOINT cap confers `SyncSend` (the sync send) — and the
notification cap does NOT confer `SyncSend`. So the attenuated "may poke, may not message" is a real,
distinct, INHABITED authority — the new expressivity the design names. (`oref`/`badge` are not
inspected by `capAuthConferred`, so a concrete `9 0` witness is general — exactly the `SeL4Abstract`
non-vacuity convention, e.g. `egEndpoint`.) -/
theorem notify_cap_confers_notify_not_syncsend :
    Auth.Notify ∈ capAuthConferred (.NotificationCap 9 0 [.AllowWrite])
      ∧ Auth.SyncSend ∉ capAuthConferred (.NotificationCap 9 0 [.AllowWrite])
      ∧ Auth.SyncSend ∈ capAuthConferred (.EndpointCap 9 0 [.AllowWrite]) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5 — NON-VACUITY TEETH (`#guard`): both polarities BITE, on concrete badges.

The badge lattice: `mask = 0b001` admits badge `0b001` (within) but REFUSES badge `0b100` (bit `0b100`
not in the mask). Attenuating `0b101 → 0b001` (drop the `0b100` bit) is a NARROWING (commits) and the
narrower cap admits strictly fewer badges; `0b001 → 0b101` is a WIDENING (refused). These are the Lean
mirrors of the gate teeth the design's Step-1 spec names. -/

section Witnesses

/-- A concrete notify cap: target object `9`, rights `signature`, badge-mask `0b101` (may wake for the
two task-kinds bits `0b001` and `0b100`). -/
def egCap : NotifyCap := { target := 9, rights := .signature, badgeMask := 0b101 }

/-! ### GATE TEETH — a within-mask signal COMMITS; an out-of-mask signal REFUSES. -/

-- COMMITS: badge `0b001` is within the mask `0b101` ⇒ `signalGated` is `some`, OR'ing `0b001` in.
#guard (signalGated egCap Notification.empty 0b001).isSome
#guard signalGated egCap Notification.empty 0b001 == some (Notification.empty.signal 0b001)
-- COMMITS: badge `0b100` (the OTHER held bit) is within the mask ⇒ commits.
#guard (signalGated egCap Notification.empty 0b100).isSome
-- REFUSES: badge `0b010` has a bit (`0b010`) NOT in the mask `0b101` ⇒ `none` (fail-closed).
#guard (signalGated egCap Notification.empty 0b010).isNone
-- REFUSES: badge `0b111` exceeds the mask (the `0b010` bit) ⇒ `none`.
#guard (signalGated egCap Notification.empty 0b111).isNone
-- The committed badge OR's into the accumulator EXACTLY (no truncation): signalling 0b001 then 0b100
-- through the cap accumulates to 0b101 (the seL4 badge-OR, gated).
#guard
  match signalGated egCap Notification.empty 0b001 with
  | some n1 => (match signalGated egCap n1 0b100 with
               | some n2 => n2.badge == 0b101
               | none => false)
  | none => false

/-! ### NON-AMPLIFICATION — attenuating narrows the mask; a widening is refused; the narrower cap
admits strictly FEWER badges. -/

-- COMMITS: attenuate the rights `signature → impossible` (a narrowing) AND the mask `0b101 → 0b001`
-- (drop the 0b100 bit, a narrowing) ⇒ `some`, holding exactly the narrower rights + mask.
#guard (egCap.attenuateNotify .impossible 0b001).isSome
#guard egCap.attenuateNotify .impossible 0b001
  == some { target := 9, rights := .impossible, badgeMask := 0b001 }
-- The ATTENUATED cap (mask 0b001) now REFUSES badge 0b100 — which the ORIGINAL cap ADMITTED.
-- Attenuation strictly shrank the admissible set (no-amplification, witnessed).
#guard egCap.signalAdmissible 0b100                              -- original admits 0b100
#guard
  match egCap.attenuateNotify .impossible 0b001 with
  | some c => !c.signalAdmissible 0b100                          -- attenuated REFUSES 0b100
  | none => false
-- …and the attenuated cap STILL admits 0b001 (it narrowed, did not go dark): both polarities.
#guard
  match egCap.attenuateNotify .impossible 0b001 with
  | some c => c.signalAdmissible 0b001
  | none => false

-- REFUSES (mask widening): attenuate the mask `0b101 → 0b111` (add the 0b010 bit, not held) ⇒ `none`.
#guard (egCap.attenuateNotify .impossible 0b111).isNone
-- REFUSES (mask widening to a disjoint bit): `0b101 → 0b010` ⇒ `none` (0b010 not within 0b101).
#guard (egCap.attenuateNotify .impossible 0b010).isNone
-- REFUSES (rights widening): `signature → either` (a widening) ⇒ `none`, even with a narrowing mask.
#guard (egCap.attenuateNotify .either 0b001).isNone
-- COMMITS (the OTHER rights polarity): `signature → impossible` narrows ⇒ the gate is not constant-none.
#guard (egCap.attenuateNotify .impossible 0b101).isSome

/-! ### MASK SUB-LATTICE — reflexive, 0 the bottom, and the order is genuine (witnessed). -/

#guard maskNarrowerOrEqual 0b101 0b101          -- reflexive
#guard maskNarrowerOrEqual 0 0b101              -- 0 (signal nothing) is narrower than anything
#guard maskNarrowerOrEqual 0b001 0b101          -- 0b001 ⊆ 0b101
#guard !maskNarrowerOrEqual 0b010 0b101         -- 0b010 ⊄ 0b101 (the 0b010 bit is not held)
#guard badgeWithinMask 0b001 0b101              -- badge 0b001 within mask 0b101
#guard !badgeWithinMask 0b010 0b101             -- badge 0b010 NOT within mask 0b101

/-! ### WELL-FORMEDNESS — Notify conferred, SyncSend/Grant/Call/Reply not (the seL4 strip). -/

-- A notification cap with AllowWrite confers Notify (async wake), NOT SyncSend (sync send).
#guard (Auth.Notify ∈ capAuthConferred (.NotificationCap 9 0 [.AllowWrite]) : Bool)
#guard !(Auth.SyncSend ∈ capAuthConferred (.NotificationCap 9 0 [.AllowWrite]) : Bool)
-- Even with FULL rights, a notification cap confers no Grant/Call/Reply (the strip bites).
#guard !(Auth.Grant ∈ capAuthConferred (.NotificationCap 9 0 SeL4Abstract.allRights) : Bool)
#guard !(Auth.Call ∈ capAuthConferred (.NotificationCap 9 0 SeL4Abstract.allRights) : Bool)
#guard !(Auth.Reply ∈ capAuthConferred (.NotificationCap 9 0 SeL4Abstract.allRights) : Bool)
-- The SAME AllowWrite on an ENDPOINT cap confers SyncSend (the sync dual) — the seL4 split.
#guard (Auth.SyncSend ∈ capAuthConferred (.EndpointCap 9 0 [.AllowWrite]) : Bool)

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing theorem is checked kernel-clean (no `sorry`, no extra
`axiom`, only the standard `propext`/`Classical.choice`/`Quot.sound`). -/

#assert_all_clean [
  maskNarrowerOrEqual_refl,
  maskNarrowerOrEqual_zero_bot,
  maskNarrowerOrEqual_antisymm,
  maskNarrowerOrEqual_trans,
  badgeWithinMask_mono,
  masked_eq_badge_of_within,
  attenuateNotify_narrows,
  attenuateNotify_refuses_mask_widening,
  attenuateNotify_refuses_rights_widening,
  signalAdmissible_attenuate_no_amplify,
  signalGated_commits_of_admissible,
  signalGated_refuses_of_inadmissible,
  notificationCap_confers_at_most_notify_read,
  notificationCap_never_grant,
  notificationCap_never_call,
  notificationCap_never_reply,
  notify_distinct_from_sync,
  notify_cap_confers_notify_not_syncsend
]

end Dregg2.Firmament.NotifyAuthority
